import V185TrunkScan19Chunk013

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_141276 : List Nat := [2, 2, 6, 1, 1, 2, 5]
def baseStart_141276 : Nat := 118140960795 + 141276 * 2 ^ 59
def prefixEnd_141276 : Nat := 4983230072969 + 3 ^ 40 * 141276 * 2
def baseEnd_141276 : Nat := 14329381322408788286477

theorem tailTrace_141276 : CollatzResearch.WordTrace tailWord_141276 prefixEnd_141276 14329381322408788286477 := by
  unfold tailWord_141276
  simp only [CollatzResearch.WordTrace]
  refine ⟨2576379518094327432489841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3435172690792436576653121 2576379518094327432489841)
  ·
    refine ⟨1932284638570745574367381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2576379518094327432489841 1932284638570745574367381)
    ·
      refine ⟨90575842433003698798471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1932284638570745574367381 90575842433003698798471)
      ·
        refine ⟨135863763649505548197707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90575842433003698798471 135863763649505548197707)
        ·
          refine ⟨203795645474258322296561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135863763649505548197707 203795645474258322296561)
          ·
            refine ⟨152846734105693741722421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203795645474258322296561 152846734105693741722421)
            ·
              refine ⟨14329381322408788286477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 152846734105693741722421 14329381322408788286477)
              ·
                rfl

theorem cell19_141276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 5].length) (baseStart_141276 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_141276 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_141276 prefixEnd_141276 := by exact prefixLift 141276
  have htrace : WordTrace (prefixWord ++ tailWord_141276) baseStart_141276 baseEnd_141276 := by
    simpa [prefixWord, tailWord_141276, baseEnd_141276] using wordTrace_append hprefix tailTrace_141276
  have hstable : (prefixWord ++ tailWord_141276).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141276).length < 2 ^ (prefixWord ++ tailWord_141276).sum := by decide
  have hdescent : baseEnd_141276 < baseStart_141276 := by decide
  rcases family_descends (prefixWord ++ tailWord_141276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141352 : List Nat := [2, 1, 5, 3, 2, 1, 1, 4]
def baseStart_141352 : Nat := 118140960795 + 141352 * 2 ^ 59
def prefixEnd_141352 : Nat := 4983230072969 + 3 ^ 40 * 141352 * 2
def baseEnd_141352 : Nat := 43011269614480707170335

theorem tailTrace_141352 : CollatzResearch.WordTrace tailWord_141352 prefixEnd_141352 43011269614480707170335 := by
  unfold tailWord_141352
  simp only [CollatzResearch.WordTrace]
  refine ⟨2577765491956659922373155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3437020655942213229830873 2577765491956659922373155)
  ·
    refine ⟨3866648237934989883559733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2577765491956659922373155 3866648237934989883559733)
    ·
      refine ⟨362498272306405301583725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3866648237934989883559733 362498272306405301583725)
      ·
        refine ⟨135936852114901988093897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 362498272306405301583725 135936852114901988093897)
        ·
          refine ⟨101952639086176491070423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135936852114901988093897 101952639086176491070423)
          ·
            refine ⟨152928958629264736605635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101952639086176491070423 152928958629264736605635)
            ·
              refine ⟨229393437943897104908453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152928958629264736605635 229393437943897104908453)
              ·
                refine ⟨43011269614480707170335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 229393437943897104908453 43011269614480707170335)
                ·
                  rfl

theorem cell19_141352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 4].length) (baseStart_141352 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_141352 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_141352 prefixEnd_141352 := by exact prefixLift 141352
  have htrace : WordTrace (prefixWord ++ tailWord_141352) baseStart_141352 baseEnd_141352 := by
    simpa [prefixWord, tailWord_141352, baseEnd_141352] using wordTrace_append hprefix tailTrace_141352
  have hstable : (prefixWord ++ tailWord_141352).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141352).length < 2 ^ (prefixWord ++ tailWord_141352).sum := by decide
  have hdescent : baseEnd_141352 < baseStart_141352 := by decide
  rcases family_descends (prefixWord ++ tailWord_141352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141417 : List Nat := [1, 2, 1, 1, 1, 5, 2, 6]
def baseStart_141417 : Nat := 118140960795 + 141417 * 2 ^ 59
def prefixEnd_141417 : Nat := 4983230072969 + 3 ^ 40 * 141417 * 2
def baseEnd_141417 : Nat := 43031048128579815725713

theorem tailTrace_141417 : CollatzResearch.WordTrace tailWord_141417 prefixEnd_141417 43031048128579815725713 := by
  unfold tailWord_141417
  simp only [CollatzResearch.WordTrace]
  refine ⟨5157901728677835945862505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3438601152451890630575003 5157901728677835945862505)
  ·
    refine ⟨3868426296508376959396879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5157901728677835945862505 3868426296508376959396879)
    ·
      refine ⟨5802639444762565439095319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3868426296508376959396879 5802639444762565439095319)
      ·
        refine ⟨8703959167143848158642979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5802639444762565439095319 8703959167143848158642979)
        ·
          refine ⟨13055938750715772237964469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8703959167143848158642979 13055938750715772237964469)
          ·
            refine ⟨1223994257879603647309169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13055938750715772237964469 1223994257879603647309169)
            ·
              refine ⟨917995693409702735481877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1223994257879603647309169 917995693409702735481877)
              ·
                refine ⟨43031048128579815725713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 917995693409702735481877 43031048128579815725713)
                ·
                  rfl

theorem cell19_141417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 6].length) (baseStart_141417 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_141417 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_141417 prefixEnd_141417 := by exact prefixLift 141417
  have htrace : WordTrace (prefixWord ++ tailWord_141417) baseStart_141417 baseEnd_141417 := by
    simpa [prefixWord, tailWord_141417, baseEnd_141417] using wordTrace_append hprefix tailTrace_141417
  have hstable : (prefixWord ++ tailWord_141417).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141417).length < 2 ^ (prefixWord ++ tailWord_141417).sum := by decide
  have hdescent : baseEnd_141417 < baseStart_141417 := by decide
  rcases family_descends (prefixWord ++ tailWord_141417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141430 : List Nat := [5, 1, 1, 2, 1, 4, 2, 3]
def baseStart_141430 : Nat := 118140960795 + 141430 * 2 ^ 59
def prefixEnd_141430 : Nat := 4983230072969 + 3 ^ 40 * 141430 * 2
def baseEnd_141430 : Nat := 43035003831399637436789

theorem tailTrace_141430 : CollatzResearch.WordTrace tailWord_141430 prefixEnd_141430 43035003831399637436789 := by
  unfold tailWord_141430
  simp only [CollatzResearch.WordTrace]
  refine ⟨322398492351921197880359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3438917251753826110723829 322398492351921197880359)
  ·
    refine ⟨483597738527881796820539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 322398492351921197880359 483597738527881796820539)
    ·
      refine ⟨725396607791822695230809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 483597738527881796820539 725396607791822695230809)
      ·
        refine ⟨544047455843867021423107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 725396607791822695230809 544047455843867021423107)
        ·
          refine ⟨816071183765800532134661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 544047455843867021423107 816071183765800532134661)
          ·
            refine ⟨153013346956087599775249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 816071183765800532134661 153013346956087599775249)
            ·
              refine ⟨114760010217065699831437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153013346956087599775249 114760010217065699831437)
              ·
                refine ⟨43035003831399637436789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114760010217065699831437 43035003831399637436789)
                ·
                  rfl

theorem cell19_141430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_141430 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_141430 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_141430 prefixEnd_141430 := by exact prefixLift 141430
  have htrace : WordTrace (prefixWord ++ tailWord_141430) baseStart_141430 baseEnd_141430 := by
    simpa [prefixWord, tailWord_141430, baseEnd_141430] using wordTrace_append hprefix tailTrace_141430
  have hstable : (prefixWord ++ tailWord_141430).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141430).length < 2 ^ (prefixWord ++ tailWord_141430).sum := by decide
  have hdescent : baseEnd_141430 < baseStart_141430 := by decide
  rcases family_descends (prefixWord ++ tailWord_141430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141472 : List Nat := [2, 1, 1, 4, 2, 3, 2, 4]
def baseStart_141472 : Nat := 118140960795 + 141472 * 2 ^ 59
def prefixEnd_141472 : Nat := 4983230072969 + 3 ^ 40 * 141472 * 2
def baseEnd_141472 : Nat := 43047783794355984503341

theorem tailTrace_141472 : CollatzResearch.WordTrace tailWord_141472 prefixEnd_141472 43047783794355984503341 := by
  unfold tailWord_141472
  simp only [CollatzResearch.WordTrace]
  refine ⟨2579953871739290169557335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3439938495652386892743113 2579953871739290169557335)
  ·
    refine ⟨3869930807608935254336003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2579953871739290169557335 3869930807608935254336003)
    ·
      refine ⟨5804896211413402881504005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3869930807608935254336003 5804896211413402881504005)
      ·
        refine ⟨1088418039640013040282001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5804896211413402881504005 1088418039640013040282001)
        ·
          refine ⟨816313529730009780211501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1088418039640013040282001 816313529730009780211501)
          ·
            refine ⟨306117573648753667579313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 816313529730009780211501 306117573648753667579313)
            ·
              refine ⟨229588180236565250684485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 306117573648753667579313 229588180236565250684485)
              ·
                refine ⟨43047783794355984503341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 229588180236565250684485 43047783794355984503341)
                ·
                  rfl

theorem cell19_141472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_141472 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_141472 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_141472 prefixEnd_141472 := by exact prefixLift 141472
  have htrace : WordTrace (prefixWord ++ tailWord_141472) baseStart_141472 baseEnd_141472 := by
    simpa [prefixWord, tailWord_141472, baseEnd_141472] using wordTrace_append hprefix tailTrace_141472
  have hstable : (prefixWord ++ tailWord_141472).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141472).length < 2 ^ (prefixWord ++ tailWord_141472).sum := by decide
  have hdescent : baseEnd_141472 < baseStart_141472 := by decide
  rcases family_descends (prefixWord ++ tailWord_141472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141525 : List Nat := [1, 3, 2, 4, 3, 1, 1, 4]
def baseStart_141525 : Nat := 118140960795 + 141525 * 2 ^ 59
def prefixEnd_141525 : Nat := 4983230072969 + 3 ^ 40 * 141525 * 2
def baseEnd_141525 : Nat := 43063910890467565325419

theorem tailTrace_141525 : CollatzResearch.WordTrace tailWord_141525 prefixEnd_141525 43063910890467565325419 := by
  unfold tailWord_141525
  simp only [CollatzResearch.WordTrace]
  refine ⟨5161840812286570390794029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3441227208191046927196019 5161840812286570390794029)
  ·
    refine ⟨1935690304607463896547761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5161840812286570390794029 1935690304607463896547761)
    ·
      refine ⟨1451767728455597922410821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1935690304607463896547761 1451767728455597922410821)
      ·
        refine ⟨272206449085424610452029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1451767728455597922410821 272206449085424610452029)
        ·
          refine ⟨102077418407034228919511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 272206449085424610452029 102077418407034228919511)
          ·
            refine ⟨153116127610551343379267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102077418407034228919511 153116127610551343379267)
            ·
              refine ⟨229674191415827015068901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153116127610551343379267 229674191415827015068901)
              ·
                refine ⟨43063910890467565325419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 229674191415827015068901 43063910890467565325419)
                ·
                  rfl

theorem cell19_141525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 4].length) (baseStart_141525 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_141525 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_141525 prefixEnd_141525 := by exact prefixLift 141525
  have htrace : WordTrace (prefixWord ++ tailWord_141525) baseStart_141525 baseEnd_141525 := by
    simpa [prefixWord, tailWord_141525, baseEnd_141525] using wordTrace_append hprefix tailTrace_141525
  have hstable : (prefixWord ++ tailWord_141525).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141525).length < 2 ^ (prefixWord ++ tailWord_141525).sum := by decide
  have hdescent : baseEnd_141525 < baseStart_141525 := by decide
  rcases family_descends (prefixWord ++ tailWord_141525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141548 : List Nat := [2, 2, 1, 1, 2, 3, 5, 3]
def baseStart_141548 : Nat := 118140960795 + 141548 * 2 ^ 59
def prefixEnd_141548 : Nat := 4983230072969 + 3 ^ 40 * 141548 * 2
def baseEnd_141548 : Nat := 43070909441610326814245

theorem tailTrace_141548 : CollatzResearch.WordTrace tailWord_141548 prefixEnd_141548 43070909441610326814245 := by
  unfold tailWord_141548
  simp only [CollatzResearch.WordTrace]
  refine ⟨2581339845601622659440649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3441786460802163545920865 2581339845601622659440649)
  ·
    refine ⟨1936004884201216994580487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2581339845601622659440649 1936004884201216994580487)
    ·
      refine ⟨2904007326301825491870731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1936004884201216994580487 2904007326301825491870731)
      ·
        refine ⟨4356010989452738237806097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2904007326301825491870731 4356010989452738237806097)
        ·
          refine ⟨3267008242089553678354573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4356010989452738237806097 3267008242089553678354573)
          ·
            refine ⟨1225128090783582629382965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3267008242089553678354573 1225128090783582629382965)
            ·
              refine ⟨114855758510960871504653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1225128090783582629382965 114855758510960871504653)
              ·
                refine ⟨43070909441610326814245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114855758510960871504653 43070909441610326814245)
                ·
                  rfl

theorem cell19_141548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 3].length) (baseStart_141548 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_141548 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_141548 prefixEnd_141548 := by exact prefixLift 141548
  have htrace : WordTrace (prefixWord ++ tailWord_141548) baseStart_141548 baseEnd_141548 := by
    simpa [prefixWord, tailWord_141548, baseEnd_141548] using wordTrace_append hprefix tailTrace_141548
  have hstable : (prefixWord ++ tailWord_141548).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141548).length < 2 ^ (prefixWord ++ tailWord_141548).sum := by decide
  have hdescent : baseEnd_141548 < baseStart_141548 := by decide
  rcases family_descends (prefixWord ++ tailWord_141548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141569 : List Nat := [1, 2, 4, 1, 1, 2, 8]
def baseStart_141569 : Nat := 118140960795 + 141569 * 2 ^ 59
def prefixEnd_141569 : Nat := 4983230072969 + 3 ^ 40 * 141569 * 2
def baseEnd_141569 : Nat := 14359099807696166782507

theorem tailTrace_141569 : CollatzResearch.WordTrace tailWord_141569 prefixEnd_141569 14359099807696166782507 := by
  unfold tailWord_141569
  simp only [CollatzResearch.WordTrace]
  refine ⟨5163445624127165905395761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3442297082751443936930507 5163445624127165905395761)
  ·
    refine ⟨3872584218095374429046821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5163445624127165905395761 3872584218095374429046821)
    ·
      refine ⟨726109540892882705446279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3872584218095374429046821 726109540892882705446279)
      ·
        refine ⟨1089164311339324058169419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 726109540892882705446279 1089164311339324058169419)
        ·
          refine ⟨1633746467008986087254129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1089164311339324058169419 1633746467008986087254129)
          ·
            refine ⟨1225309850256739565440597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1633746467008986087254129 1225309850256739565440597)
            ·
              refine ⟨14359099807696166782507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1225309850256739565440597 14359099807696166782507)
              ·
                rfl

theorem cell19_141569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 8].length) (baseStart_141569 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_141569 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_141569 prefixEnd_141569 := by exact prefixLift 141569
  have htrace : WordTrace (prefixWord ++ tailWord_141569) baseStart_141569 baseEnd_141569 := by
    simpa [prefixWord, tailWord_141569, baseEnd_141569] using wordTrace_append hprefix tailTrace_141569
  have hstable : (prefixWord ++ tailWord_141569).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141569).length < 2 ^ (prefixWord ++ tailWord_141569).sum := by decide
  have hdescent : baseEnd_141569 < baseStart_141569 := by decide
  rcases family_descends (prefixWord ++ tailWord_141569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141605 : List Nat := [1, 3, 1, 2, 5, 1, 1, 5]
def baseStart_141605 : Nat := 118140960795 + 141605 * 2 ^ 59
def prefixEnd_141605 : Nat := 4983230072969 + 3 ^ 40 * 141605 * 2
def baseEnd_141605 : Nat := 43088253677051083547423

theorem tailTrace_141605 : CollatzResearch.WordTrace tailWord_141605 prefixEnd_141605 43088253677051083547423 := by
  unfold tailWord_141605
  simp only [CollatzResearch.WordTrace]
  refine ⟨5164758651996744053706269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3443172434664496035804179 5164758651996744053706269)
  ·
    refine ⟨1936784494498779020139851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5164758651996744053706269 1936784494498779020139851)
    ·
      refine ⟨2905176741748168530209777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1936784494498779020139851 2905176741748168530209777)
      ·
        refine ⟨2178882556311126397657333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2905176741748168530209777 2178882556311126397657333)
        ·
          refine ⟨204270239654168099780375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2178882556311126397657333 204270239654168099780375)
          ·
            refine ⟨306405359481252149670563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204270239654168099780375 306405359481252149670563)
            ·
              refine ⟨459608039221878224505845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306405359481252149670563 459608039221878224505845)
              ·
                refine ⟨43088253677051083547423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 459608039221878224505845 43088253677051083547423)
                ·
                  rfl

theorem cell19_141605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 5].length) (baseStart_141605 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_141605 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_141605 prefixEnd_141605 := by exact prefixLift 141605
  have htrace : WordTrace (prefixWord ++ tailWord_141605) baseStart_141605 baseEnd_141605 := by
    simpa [prefixWord, tailWord_141605, baseEnd_141605] using wordTrace_append hprefix tailTrace_141605
  have hstable : (prefixWord ++ tailWord_141605).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141605).length < 2 ^ (prefixWord ++ tailWord_141605).sum := by decide
  have hdescent : baseEnd_141605 < baseStart_141605 := by decide
  rcases family_descends (prefixWord ++ tailWord_141605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141626 : List Nat := [3, 1, 1, 1, 4, 2, 7]
def baseStart_141626 : Nat := 118140960795 + 141626 * 2 ^ 59
def prefixEnd_141626 : Nat := 4983230072969 + 3 ^ 40 * 141626 * 2
def baseEnd_141626 : Nat := 14364881219509752360233

theorem tailTrace_141626 : CollatzResearch.WordTrace tailWord_141626 prefixEnd_141626 14364881219509752360233 := by
  unfold tailWord_141626
  simp only [CollatzResearch.WordTrace]
  refine ⟨1291381146230166160055183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3443683056613776426813821 1291381146230166160055183)
  ·
    refine ⟨1937071719345249240082775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1291381146230166160055183 1937071719345249240082775)
    ·
      refine ⟨2905607579017873860124163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1937071719345249240082775 2905607579017873860124163)
      ·
        refine ⟨4358411368526810790186245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2905607579017873860124163 4358411368526810790186245)
        ·
          refine ⟨817202131598777023159921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4358411368526810790186245 817202131598777023159921)
          ·
            refine ⟨612901598699082767369941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 817202131598777023159921 612901598699082767369941)
            ·
              refine ⟨14364881219509752360233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 612901598699082767369941 14364881219509752360233)
              ·
                rfl

theorem cell19_141626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 7].length) (baseStart_141626 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_141626 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_141626 prefixEnd_141626 := by exact prefixLift 141626
  have htrace : WordTrace (prefixWord ++ tailWord_141626) baseStart_141626 baseEnd_141626 := by
    simpa [prefixWord, tailWord_141626, baseEnd_141626] using wordTrace_append hprefix tailTrace_141626
  have hstable : (prefixWord ++ tailWord_141626).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141626).length < 2 ^ (prefixWord ++ tailWord_141626).sum := by decide
  have hdescent : baseEnd_141626 < baseStart_141626 := by decide
  rcases family_descends (prefixWord ++ tailWord_141626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141772 : List Nat := [2, 2, 1, 4, 4, 1, 2, 3]
def baseStart_141772 : Nat := 118140960795 + 141772 * 2 ^ 59
def prefixEnd_141772 : Nat := 4983230072969 + 3 ^ 40 * 141772 * 2
def baseEnd_141772 : Nat := 43139069244044177835857

theorem tailTrace_141772 : CollatzResearch.WordTrace tailWord_141772 prefixEnd_141772 43139069244044177835857 := by
  unfold tailWord_141772
  simp only [CollatzResearch.WordTrace]
  refine ⟨2585424821195865787517785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3447233094927821050023713 2585424821195865787517785)
  ·
    refine ⟨1939068615896899340638339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2585424821195865787517785 1939068615896899340638339)
    ·
      refine ⟨2908602923845349010957509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1939068615896899340638339 2908602923845349010957509)
      ·
        refine ⟨545363048221002939554533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2908602923845349010957509 545363048221002939554533)
        ·
          refine ⟨102255571541438051166475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 545363048221002939554533 102255571541438051166475)
          ·
            refine ⟨153383357312157076749713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102255571541438051166475 153383357312157076749713)
            ·
              refine ⟨115037517984117807562285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153383357312157076749713 115037517984117807562285)
              ·
                refine ⟨43139069244044177835857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115037517984117807562285 43139069244044177835857)
                ·
                  rfl

theorem cell19_141772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 3].length) (baseStart_141772 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_141772 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_141772 prefixEnd_141772 := by exact prefixLift 141772
  have htrace : WordTrace (prefixWord ++ tailWord_141772) baseStart_141772 baseEnd_141772 := by
    simpa [prefixWord, tailWord_141772, baseEnd_141772] using wordTrace_append hprefix tailTrace_141772
  have hstable : (prefixWord ++ tailWord_141772).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141772).length < 2 ^ (prefixWord ++ tailWord_141772).sum := by decide
  have hdescent : baseEnd_141772 < baseStart_141772 := by decide
  rcases family_descends (prefixWord ++ tailWord_141772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141795 : List Nat := [1, 1, 1, 6, 3, 2, 5]
def baseStart_141795 : Nat := 118140960795 + 141795 * 2 ^ 59
def prefixEnd_141795 : Nat := 4983230072969 + 3 ^ 40 * 141795 * 2
def baseEnd_141795 : Nat := 14382022598395646441561

theorem tailTrace_141795 : CollatzResearch.WordTrace tailWord_141795 prefixEnd_141795 14382022598395646441561 := by
  unfold tailWord_141795
  simp only [CollatzResearch.WordTrace]
  refine ⟨5171688521308406503122839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3447792347538937668748559 5171688521308406503122839)
  ·
    refine ⟨7757532781962609754684259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5171688521308406503122839 7757532781962609754684259)
    ·
      refine ⟨11636299172943914632026389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7757532781962609754684259 11636299172943914632026389)
      ·
        refine ⟨545451523731745998376237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11636299172943914632026389 545451523731745998376237)
        ·
          refine ⟨204544321399404749391089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 545451523731745998376237 204544321399404749391089)
          ·
            refine ⟨153408241049553562043317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204544321399404749391089 153408241049553562043317)
            ·
              refine ⟨14382022598395646441561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 153408241049553562043317 14382022598395646441561)
              ·
                rfl

theorem cell19_141795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 5].length) (baseStart_141795 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_141795 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_141795 prefixEnd_141795 := by exact prefixLift 141795
  have htrace : WordTrace (prefixWord ++ tailWord_141795) baseStart_141795 baseEnd_141795 := by
    simpa [prefixWord, tailWord_141795, baseEnd_141795] using wordTrace_append hprefix tailTrace_141795
  have hstable : (prefixWord ++ tailWord_141795).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141795).length < 2 ^ (prefixWord ++ tailWord_141795).sum := by decide
  have hdescent : baseEnd_141795 < baseStart_141795 := by decide
  rcases family_descends (prefixWord ++ tailWord_141795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141814 : List Nat := [5, 1, 1, 1, 2, 1, 4, 4]
def baseStart_141814 : Nat := 118140960795 + 141814 * 2 ^ 59
def prefixEnd_141814 : Nat := 4983230072969 + 3 ^ 40 * 141814 * 2
def baseEnd_141814 : Nat := 43151849207000524902409

theorem tailTrace_141814 : CollatzResearch.WordTrace tailWord_141814 prefixEnd_141814 43151849207000524902409 := by
  unfold tailWord_141814
  simp only [CollatzResearch.WordTrace]
  refine ⟨323273844264973296754031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3448254338826381832042997 323273844264973296754031)
  ·
    refine ⟨484910766397459945131047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 323273844264973296754031 484910766397459945131047)
    ·
      refine ⟨727366149596189917696571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 484910766397459945131047 727366149596189917696571)
      ·
        refine ⟨1091049224394284876544857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 727366149596189917696571 1091049224394284876544857)
        ·
          refine ⟨818286918295713657408643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1091049224394284876544857 818286918295713657408643)
          ·
            refine ⟨1227430377443570486112965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 818286918295713657408643 1227430377443570486112965)
            ·
              refine ⟨230143195770669466146181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1227430377443570486112965 230143195770669466146181)
              ·
                refine ⟨43151849207000524902409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 230143195770669466146181 43151849207000524902409)
                ·
                  rfl

theorem cell19_141814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_141814 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_141814 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_141814 prefixEnd_141814 := by exact prefixLift 141814
  have htrace : WordTrace (prefixWord ++ tailWord_141814) baseStart_141814 baseEnd_141814 := by
    simpa [prefixWord, tailWord_141814, baseEnd_141814] using wordTrace_append hprefix tailTrace_141814
  have hstable : (prefixWord ++ tailWord_141814).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141814).length < 2 ^ (prefixWord ++ tailWord_141814).sum := by decide
  have hdescent : baseEnd_141814 < baseStart_141814 := by decide
  rcases family_descends (prefixWord ++ tailWord_141814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141816 : List Nat := [2, 1, 2, 1, 1, 4, 4, 4]
def baseStart_141816 : Nat := 118140960795 + 141816 * 2 ^ 59
def prefixEnd_141816 : Nat := 4983230072969 + 3 ^ 40 * 141816 * 2
def baseEnd_141816 : Nat := 43152457776665112857959

theorem tailTrace_141816 : CollatzResearch.WordTrace tailWord_141816 prefixEnd_141816 43152457776665112857959 := by
  unfold tailWord_141816
  simp only [CollatzResearch.WordTrace]
  refine ⟨2586227227116163544818651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3448302969488218059758201 2586227227116163544818651)
  ·
    refine ⟨3879340840674245317227977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2586227227116163544818651 3879340840674245317227977)
    ·
      refine ⟨2909505630505683987920983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3879340840674245317227977 2909505630505683987920983)
      ·
        refine ⟨4364258445758525981881475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2909505630505683987920983 4364258445758525981881475)
        ·
          refine ⟨6546387668637788972822213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4364258445758525981881475 6546387668637788972822213)
          ·
            refine ⟨1227447687869585432404165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6546387668637788972822213 1227447687869585432404165)
            ·
              refine ⟨230146441475547268575781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1227447687869585432404165 230146441475547268575781)
              ·
                refine ⟨43152457776665112857959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 230146441475547268575781 43152457776665112857959)
                ·
                  rfl

theorem cell19_141816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_141816 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_141816 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_141816 prefixEnd_141816 := by exact prefixLift 141816
  have htrace : WordTrace (prefixWord ++ tailWord_141816) baseStart_141816 baseEnd_141816 := by
    simpa [prefixWord, tailWord_141816, baseEnd_141816] using wordTrace_append hprefix tailTrace_141816
  have hstable : (prefixWord ++ tailWord_141816).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141816).length < 2 ^ (prefixWord ++ tailWord_141816).sum := by decide
  have hdescent : baseEnd_141816 < baseStart_141816 := by decide
  rcases family_descends (prefixWord ++ tailWord_141816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141835 : List Nat := [1, 1, 1, 1, 7, 1, 2, 5]
def baseStart_141835 : Nat := 118140960795 + 141835 * 2 ^ 59
def prefixEnd_141835 : Nat := 4983230072969 + 3 ^ 40 * 141835 * 2
def baseEnd_141835 : Nat := 43158239188478698435685

theorem tailTrace_141835 : CollatzResearch.WordTrace tailWord_141835 prefixEnd_141835 43158239188478698435685 := by
  unfold tailWord_141835
  simp only [CollatzResearch.WordTrace]
  refine ⟨5173147441163493334578959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3448764960775662223052639 5173147441163493334578959)
  ·
    refine ⟨7759721161745240001868439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5173147441163493334578959 7759721161745240001868439)
    ·
      refine ⟨11639581742617860002802659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7759721161745240001868439 11639581742617860002802659)
      ·
        refine ⟨17459372613926790004203989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11639581742617860002802659 17459372613926790004203989)
        ·
          refine ⟨409204045638909140723531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 17459372613926790004203989 409204045638909140723531)
          ·
            refine ⟨613806068458363711085297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409204045638909140723531 613806068458363711085297)
            ·
              refine ⟨460354551343772783313973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 613806068458363711085297 460354551343772783313973)
              ·
                refine ⟨43158239188478698435685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 460354551343772783313973 43158239188478698435685)
                ·
                  rfl

theorem cell19_141835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 5].length) (baseStart_141835 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_141835 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_141835 prefixEnd_141835 := by exact prefixLift 141835
  have htrace : WordTrace (prefixWord ++ tailWord_141835) baseStart_141835 baseEnd_141835 := by
    simpa [prefixWord, tailWord_141835, baseEnd_141835] using wordTrace_append hprefix tailTrace_141835
  have hstable : (prefixWord ++ tailWord_141835).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141835).length < 2 ^ (prefixWord ++ tailWord_141835).sum := by decide
  have hdescent : baseEnd_141835 < baseStart_141835 := by decide
  rcases family_descends (prefixWord ++ tailWord_141835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141873 : List Nat := [1, 2, 2, 3, 1, 1, 5, 4]
def baseStart_141873 : Nat := 118140960795 + 141873 * 2 ^ 59
def prefixEnd_141873 : Nat := 4983230072969 + 3 ^ 40 * 141873 * 2
def baseEnd_141873 : Nat := 43169802012105869591137

theorem tailTrace_141873 : CollatzResearch.WordTrace tailWord_141873 prefixEnd_141873 43169802012105869591137 := by
  unfold tailWord_141873
  simp only [CollatzResearch.WordTrace]
  refine ⟨5174533415025825824462273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3449688943350550549641515 5174533415025825824462273)
  ·
    refine ⟨3880900061269369368346705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5174533415025825824462273 3880900061269369368346705)
    ·
      refine ⟨2910675045952027026260029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3880900061269369368346705 2910675045952027026260029)
      ·
        refine ⟨1091503142232010134847511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2910675045952027026260029 1091503142232010134847511)
        ·
          refine ⟨1637254713348015202271267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1091503142232010134847511 1637254713348015202271267)
          ·
            refine ⟨2455882070022022803406901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1637254713348015202271267 2455882070022022803406901)
            ·
              refine ⟨230238944064564637819397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2455882070022022803406901 230238944064564637819397)
              ·
                refine ⟨43169802012105869591137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 230238944064564637819397 43169802012105869591137)
                ·
                  rfl

theorem cell19_141873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 4].length) (baseStart_141873 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_141873 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_141873 prefixEnd_141873 := by exact prefixLift 141873
  have htrace : WordTrace (prefixWord ++ tailWord_141873) baseStart_141873 baseEnd_141873 := by
    simpa [prefixWord, tailWord_141873, baseEnd_141873] using wordTrace_append hprefix tailTrace_141873
  have hstable : (prefixWord ++ tailWord_141873).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141873).length < 2 ^ (prefixWord ++ tailWord_141873).sum := by decide
  have hdescent : baseEnd_141873 < baseStart_141873 := by decide
  rcases family_descends (prefixWord ++ tailWord_141873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141886 : List Nat := [4, 2, 1, 4, 1, 1, 3, 3]
def baseStart_141886 : Nat := 118140960795 + 141886 * 2 ^ 59
def prefixEnd_141886 : Nat := 4983230072969 + 3 ^ 40 * 141886 * 2
def baseEnd_141886 : Nat := 43173757714925691302213

theorem tailTrace_141886 : CollatzResearch.WordTrace tailWord_141886 prefixEnd_141886 43173757714925691302213 := by
  unfold tailWord_141886
  simp only [CollatzResearch.WordTrace]
  refine ⟨646875945497341130585689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3450005042652486029790341 646875945497341130585689)
  ·
    refine ⟨485156959123005847939267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 646875945497341130585689 485156959123005847939267)
    ·
      refine ⟨727735438684508771908901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 485156959123005847939267 727735438684508771908901)
      ·
        refine ⟨136450394753345394732919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 727735438684508771908901 136450394753345394732919)
        ·
          refine ⟨204675592130018092099379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136450394753345394732919 204675592130018092099379)
          ·
            refine ⟨307013388195027138149069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204675592130018092099379 307013388195027138149069)
            ·
              refine ⟨115130020573135176805901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 307013388195027138149069 115130020573135176805901)
              ·
                refine ⟨43173757714925691302213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115130020573135176805901 43173757714925691302213)
                ·
                  rfl

theorem cell19_141886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_141886 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_141886 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_141886 prefixEnd_141886 := by exact prefixLift 141886
  have htrace : WordTrace (prefixWord ++ tailWord_141886) baseStart_141886 baseEnd_141886 := by
    simpa [prefixWord, tailWord_141886, baseEnd_141886] using wordTrace_append hprefix tailTrace_141886
  have hstable : (prefixWord ++ tailWord_141886).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141886).length < 2 ^ (prefixWord ++ tailWord_141886).sum := by decide
  have hdescent : baseEnd_141886 < baseStart_141886 := by decide
  rcases family_descends (prefixWord ++ tailWord_141886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141930 : List Nat := [3, 1, 3, 2, 1, 1, 2, 6]
def baseStart_141930 : Nat := 118140960795 + 141930 * 2 ^ 59
def prefixEnd_141930 : Nat := 4983230072969 + 3 ^ 40 * 141930 * 2
def baseEnd_141930 : Nat := 43187146247546626324315

theorem tailTrace_141930 : CollatzResearch.WordTrace tailWord_141930 prefixEnd_141930 43187146247546626324315 := by
  unfold tailWord_141930
  simp only [CollatzResearch.WordTrace]
  refine ⟨1294153093954831139821811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3451074917212883039524829 1294153093954831139821811)
  ·
    refine ⟨1941229640932246709732717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1294153093954831139821811 1941229640932246709732717)
    ·
      refine ⟨727961115349592516149769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1941229640932246709732717 727961115349592516149769)
      ·
        refine ⟨545970836512194387112327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 727961115349592516149769 545970836512194387112327)
        ·
          refine ⟨818956254768291580668491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 545970836512194387112327 818956254768291580668491)
          ·
            refine ⟨1228434382152437371002737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 818956254768291580668491 1228434382152437371002737)
            ·
              refine ⟨921325786614328028252053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1228434382152437371002737 921325786614328028252053)
              ·
                refine ⟨43187146247546626324315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 921325786614328028252053 43187146247546626324315)
                ·
                  rfl

theorem cell19_141930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_141930 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_141930 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_141930 prefixEnd_141930 := by exact prefixLift 141930
  have htrace : WordTrace (prefixWord ++ tailWord_141930) baseStart_141930 baseEnd_141930 := by
    simpa [prefixWord, tailWord_141930, baseEnd_141930] using wordTrace_append hprefix tailTrace_141930
  have hstable : (prefixWord ++ tailWord_141930).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141930).length < 2 ^ (prefixWord ++ tailWord_141930).sum := by decide
  have hdescent : baseEnd_141930 < baseStart_141930 := by decide
  rcases family_descends (prefixWord ++ tailWord_141930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141985 : List Nat := [1, 2, 3, 3, 3, 1, 2, 4]
def baseStart_141985 : Nat := 118140960795 + 141985 * 2 ^ 59
def prefixEnd_141985 : Nat := 4983230072969 + 3 ^ 40 * 141985 * 2
def baseEnd_141985 : Nat := 43203881913322795101943

theorem tailTrace_141985 : CollatzResearch.WordTrace tailWord_141985 prefixEnd_141985 43203881913322795101943 := by
  unfold tailWord_141985
  simp only [CollatzResearch.WordTrace]
  refine ⟨5178618390620068952539409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3452412260413379301692939 5178618390620068952539409)
  ·
    refine ⟨3883963792965051714404557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5178618390620068952539409 3883963792965051714404557)
    ·
      refine ⟨1456486422361894392901709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3883963792965051714404557 1456486422361894392901709)
      ·
        refine ⟨546182408385710397338141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1456486422361894392901709 546182408385710397338141)
        ·
          refine ⟨204818403144641399001803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 546182408385710397338141 204818403144641399001803)
          ·
            refine ⟨307227604716962098502705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204818403144641399001803 307227604716962098502705)
            ·
              refine ⟨230420703537721573877029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 307227604716962098502705 230420703537721573877029)
              ·
                refine ⟨43203881913322795101943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 230420703537721573877029 43203881913322795101943)
                ·
                  rfl

theorem cell19_141985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 4].length) (baseStart_141985 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_141985 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_141985 prefixEnd_141985 := by exact prefixLift 141985
  have htrace : WordTrace (prefixWord ++ tailWord_141985) baseStart_141985 baseEnd_141985 := by
    simpa [prefixWord, tailWord_141985, baseEnd_141985] using wordTrace_append hprefix tailTrace_141985
  have hstable : (prefixWord ++ tailWord_141985).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141985).length < 2 ^ (prefixWord ++ tailWord_141985).sum := by decide
  have hdescent : baseEnd_141985 < baseStart_141985 := by decide
  rcases family_descends (prefixWord ++ tailWord_141985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142061 : List Nat := [1, 5, 1, 2, 1, 1, 5, 3]
def baseStart_142061 : Nat := 118140960795 + 142061 * 2 ^ 59
def prefixEnd_142061 : Nat := 4983230072969 + 3 ^ 40 * 142061 * 2
def baseEnd_142061 : Nat := 43227007560577137412847

theorem tailTrace_142061 : CollatzResearch.WordTrace tailWord_142061 prefixEnd_142061 43227007560577137412847 := by
  unfold tailWord_142061
  simp only [CollatzResearch.WordTrace]
  refine ⟨5181390338344733932306037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3454260225563155954870691 5181390338344733932306037)
  ·
    refine ⟨485755344219818806153691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5181390338344733932306037 485755344219818806153691)
    ·
      refine ⟨728633016329728209230537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 485755344219818806153691 728633016329728209230537)
      ·
        refine ⟨546474762247296156922903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 728633016329728209230537 546474762247296156922903)
        ·
          refine ⟨819712143370944235384355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 546474762247296156922903 819712143370944235384355)
          ·
            refine ⟨1229568215056416353076533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 819712143370944235384355 1229568215056416353076533)
            ·
              refine ⟨115272020161539033100925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1229568215056416353076533 115272020161539033100925)
              ·
                refine ⟨43227007560577137412847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115272020161539033100925 43227007560577137412847)
                ·
                  rfl

theorem cell19_142061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 3].length) (baseStart_142061 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_142061 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_142061 prefixEnd_142061 := by exact prefixLift 142061
  have htrace : WordTrace (prefixWord ++ tailWord_142061) baseStart_142061 baseEnd_142061 := by
    simpa [prefixWord, tailWord_142061, baseEnd_142061] using wordTrace_append hprefix tailTrace_142061
  have hstable : (prefixWord ++ tailWord_142061).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142061).length < 2 ^ (prefixWord ++ tailWord_142061).sum := by decide
  have hdescent : baseEnd_142061 < baseStart_142061 := by decide
  rcases family_descends (prefixWord ++ tailWord_142061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142116 : List Nat := [2, 3, 1, 3, 3, 2, 2, 3]
def baseStart_142116 : Nat := 118140960795 + 142116 * 2 ^ 59
def prefixEnd_142116 : Nat := 4983230072969 + 3 ^ 40 * 142116 * 2
def baseEnd_142116 : Nat := 43243743226353306190475

theorem tailTrace_142116 : CollatzResearch.WordTrace tailWord_142116 prefixEnd_142116 43243743226353306190475 := by
  unfold tailWord_142116
  simp only [CollatzResearch.WordTrace]
  refine ⟨2591698176572739162779101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3455597568763652217038801 2591698176572739162779101)
  ·
    refine ⟨971886816214777186042163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2591698176572739162779101 971886816214777186042163)
    ·
      refine ⟨1457830224322165779063245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 971886816214777186042163 1457830224322165779063245)
      ·
        refine ⟨546686334120812167148717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1457830224322165779063245 546686334120812167148717)
        ·
          refine ⟨205007375295304562680769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 546686334120812167148717 205007375295304562680769)
          ·
            refine ⟨153755531471478422010577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205007375295304562680769 153755531471478422010577)
            ·
              refine ⟨115316648603608816507933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153755531471478422010577 115316648603608816507933)
              ·
                refine ⟨43243743226353306190475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115316648603608816507933 43243743226353306190475)
                ·
                  rfl

theorem cell19_142116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 3].length) (baseStart_142116 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_142116 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_142116 prefixEnd_142116 := by exact prefixLift 142116
  have htrace : WordTrace (prefixWord ++ tailWord_142116) baseStart_142116 baseEnd_142116 := by
    simpa [prefixWord, tailWord_142116, baseEnd_142116] using wordTrace_append hprefix tailTrace_142116
  have hstable : (prefixWord ++ tailWord_142116).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142116).length < 2 ^ (prefixWord ++ tailWord_142116).sum := by decide
  have hdescent : baseEnd_142116 < baseStart_142116 := by decide
  rcases family_descends (prefixWord ++ tailWord_142116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142120 : List Nat := [2, 1, 5, 1, 1, 1, 3, 5]
def baseStart_142120 : Nat := 118140960795 + 142120 * 2 ^ 59
def prefixEnd_142120 : Nat := 4983230072969 + 3 ^ 40 * 142120 * 2
def baseEnd_142120 : Nat := 43244960365682482101575

theorem tailTrace_142120 : CollatzResearch.WordTrace tailWord_142120 prefixEnd_142120 43244960365682482101575 := by
  unfold tailWord_142120
  simp only [CollatzResearch.WordTrace]
  refine ⟨2591771122565493504351907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3455694830087324672469209 2591771122565493504351907)
  ·
    refine ⟨3887656683848240256527861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2591771122565493504351907 3887656683848240256527861)
    ·
      refine ⟨364467814110772524049487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3887656683848240256527861 364467814110772524049487)
      ·
        refine ⟨546701721166158786074231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 364467814110772524049487 546701721166158786074231)
        ·
          refine ⟨820052581749238179111347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 546701721166158786074231 820052581749238179111347)
          ·
            refine ⟨1230078872623857268667021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 820052581749238179111347 1230078872623857268667021)
            ·
              refine ⟨461279577233946475750133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1230078872623857268667021 461279577233946475750133)
              ·
                refine ⟨43244960365682482101575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 461279577233946475750133 43244960365682482101575)
                ·
                  rfl

theorem cell19_142120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_142120 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_142120 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_142120 prefixEnd_142120 := by exact prefixLift 142120
  have htrace : WordTrace (prefixWord ++ tailWord_142120) baseStart_142120 baseEnd_142120 := by
    simpa [prefixWord, tailWord_142120, baseEnd_142120] using wordTrace_append hprefix tailTrace_142120
  have hstable : (prefixWord ++ tailWord_142120).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142120).length < 2 ^ (prefixWord ++ tailWord_142120).sum := by decide
  have hdescent : baseEnd_142120 < baseStart_142120 := by decide
  rcases family_descends (prefixWord ++ tailWord_142120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142160 : List Nat := [2, 1, 1, 1, 1, 4, 3, 6]
def baseStart_142160 : Nat := 118140960795 + 142160 * 2 ^ 59
def prefixEnd_142160 : Nat := 4983230072969 + 3 ^ 40 * 142160 * 2
def baseEnd_142160 : Nat := 43257131758974241212577

theorem tailTrace_142160 : CollatzResearch.WordTrace tailWord_142160 prefixEnd_142160 43257131758974241212577 := by
  unfold tailWord_142160
  simp only [CollatzResearch.WordTrace]
  refine ⟨2592500582493036920079967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3456667443324049226773289 2592500582493036920079967)
  ·
    refine ⟨3888750873739555380119951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2592500582493036920079967 3888750873739555380119951)
    ·
      refine ⟨5833126310609333070179927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3888750873739555380119951 5833126310609333070179927)
      ·
        refine ⟨8749689465913999605269891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5833126310609333070179927 8749689465913999605269891)
        ·
          refine ⟨13124534198870999407904837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8749689465913999605269891 13124534198870999407904837)
          ·
            refine ⟨2460850162288312388982157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13124534198870999407904837 2460850162288312388982157)
            ·
              refine ⟨922818810858117145868309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2460850162288312388982157 922818810858117145868309)
              ·
                refine ⟨43257131758974241212577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 922818810858117145868309 43257131758974241212577)
                ·
                  rfl

theorem cell19_142160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_142160 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_142160 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_142160 prefixEnd_142160 := by exact prefixLift 142160
  have htrace : WordTrace (prefixWord ++ tailWord_142160) baseStart_142160 baseEnd_142160 := by
    simpa [prefixWord, tailWord_142160, baseEnd_142160] using wordTrace_append hprefix tailTrace_142160
  have hstable : (prefixWord ++ tailWord_142160).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142160).length < 2 ^ (prefixWord ++ tailWord_142160).sum := by decide
  have hdescent : baseEnd_142160 < baseStart_142160 := by decide
  rcases family_descends (prefixWord ++ tailWord_142160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142215 : List Nat := [1, 1, 4, 2, 3, 1, 3, 4]
def baseStart_142215 : Nat := 118140960795 + 142215 * 2 ^ 59
def prefixEnd_142215 : Nat := 4983230072969 + 3 ^ 40 * 142215 * 2
def baseEnd_142215 : Nat := 43273867424750409990205

theorem tailTrace_142215 : CollatzResearch.WordTrace tailWord_142215 prefixEnd_142215 43273867424750409990205 := by
  unfold tailWord_142215
  simp only [CollatzResearch.WordTrace]
  refine ⟨5187007179786818233412099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3458004786524545488941399 5187007179786818233412099)
  ·
    refine ⟨7780510769680227350118149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5187007179786818233412099 7780510769680227350118149)
    ·
      refine ⟨1458845769315042628147153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7780510769680227350118149 1458845769315042628147153)
      ·
        refine ⟨1094134326986281971110365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1458845769315042628147153 1094134326986281971110365)
        ·
          refine ⟨410300372619855739166387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1094134326986281971110365 410300372619855739166387)
          ·
            refine ⟨615450558929783608749581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410300372619855739166387 615450558929783608749581)
            ·
              refine ⟨230793959598668853281093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 615450558929783608749581 230793959598668853281093)
              ·
                refine ⟨43273867424750409990205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 230793959598668853281093 43273867424750409990205)
                ·
                  rfl

theorem cell19_142215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 4].length) (baseStart_142215 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_142215 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_142215 prefixEnd_142215 := by exact prefixLift 142215
  have htrace : WordTrace (prefixWord ++ tailWord_142215) baseStart_142215 baseEnd_142215 := by
    simpa [prefixWord, tailWord_142215, baseEnd_142215] using wordTrace_append hprefix tailTrace_142215
  have hstable : (prefixWord ++ tailWord_142215).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142215).length < 2 ^ (prefixWord ++ tailWord_142215).sum := by decide
  have hdescent : baseEnd_142215 < baseStart_142215 := by decide
  rcases family_descends (prefixWord ++ tailWord_142215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142285 : List Nat := [1, 6, 3, 1, 1, 1, 1, 5]
def baseStart_142285 : Nat := 118140960795 + 142285 * 2 ^ 59
def prefixEnd_142285 : Nat := 4983230072969 + 3 ^ 40 * 142285 * 2
def baseEnd_142285 : Nat := 43295167363010988434459

theorem tailTrace_142285 : CollatzResearch.WordTrace tailWord_142285 prefixEnd_142285 43295167363010988434459 := by
  unfold tailWord_142285
  simp only [CollatzResearch.WordTrace]
  refine ⟨5189560289533220188460309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3459706859688813458973539 5189560289533220188460309)
  ·
    refine ⟨243260638571869696334077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5189560289533220188460309 243260638571869696334077)
    ·
      refine ⟨91222739464451136125279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243260638571869696334077 91222739464451136125279)
      ·
        refine ⟨136834109196676704187919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91222739464451136125279 136834109196676704187919)
        ·
          refine ⟨205251163795015056281879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136834109196676704187919 205251163795015056281879)
          ·
            refine ⟨307876745692522584422819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205251163795015056281879 307876745692522584422819)
            ·
              refine ⟨461815118538783876634229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307876745692522584422819 461815118538783876634229)
              ·
                refine ⟨43295167363010988434459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 461815118538783876634229 43295167363010988434459)
                ·
                  rfl

theorem cell19_142285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 5].length) (baseStart_142285 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_142285 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_142285 prefixEnd_142285 := by exact prefixLift 142285
  have htrace : WordTrace (prefixWord ++ tailWord_142285) baseStart_142285 baseEnd_142285 := by
    simpa [prefixWord, tailWord_142285, baseEnd_142285] using wordTrace_append hprefix tailTrace_142285
  have hstable : (prefixWord ++ tailWord_142285).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142285).length < 2 ^ (prefixWord ++ tailWord_142285).sum := by decide
  have hdescent : baseEnd_142285 < baseStart_142285 := by decide
  rcases family_descends (prefixWord ++ tailWord_142285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142312 : List Nat := [2, 1, 4, 1, 1, 1, 9]
def baseStart_142312 : Nat := 118140960795 + 142312 * 2 ^ 59
def prefixEnd_142312 : Nat := 4983230072969 + 3 ^ 40 * 142312 * 2
def baseEnd_142312 : Nat := 14434461017827641944795

theorem tailTrace_142312 : CollatzResearch.WordTrace tailWord_142312 prefixEnd_142312 14434461017827641944795 := by
  unfold tailWord_142312
  simp only [CollatzResearch.WordTrace]
  refine ⟨2595272530217701899846595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3460363373623602533128793 2595272530217701899846595)
  ·
    refine ⟨3892908795326552849769893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2595272530217701899846595 3892908795326552849769893)
    ·
      refine ⟨729920399123728659331855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3892908795326552849769893 729920399123728659331855)
      ·
        refine ⟨1094880598685592988997783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 729920399123728659331855 1094880598685592988997783)
        ·
          refine ⟨1642320898028389483496675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1094880598685592988997783 1642320898028389483496675)
          ·
            refine ⟨2463481347042584225245013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1642320898028389483496675 2463481347042584225245013)
            ·
              refine ⟨14434461017827641944795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2463481347042584225245013 14434461017827641944795)
              ·
                rfl

theorem cell19_142312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 9].length) (baseStart_142312 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_142312 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_142312 prefixEnd_142312 := by exact prefixLift 142312
  have htrace : WordTrace (prefixWord ++ tailWord_142312) baseStart_142312 baseEnd_142312 := by
    simpa [prefixWord, tailWord_142312, baseEnd_142312] using wordTrace_append hprefix tailTrace_142312
  have hstable : (prefixWord ++ tailWord_142312).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142312).length < 2 ^ (prefixWord ++ tailWord_142312).sum := by decide
  have hdescent : baseEnd_142312 < baseStart_142312 := by decide
  rcases family_descends (prefixWord ++ tailWord_142312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142325 : List Nat := [1, 3, 5, 2, 1, 1, 2, 4]
def baseStart_142325 : Nat := 118140960795 + 142325 * 2 ^ 59
def prefixEnd_142325 : Nat := 4983230072969 + 3 ^ 40 * 142325 * 2
def baseEnd_142325 : Nat := 43307338756302747545461

theorem tailTrace_142325 : CollatzResearch.WordTrace tailWord_142325 prefixEnd_142325 43307338756302747545461 := by
  unfold tailWord_142325
  simp only [CollatzResearch.WordTrace]
  refine ⟨5191019209388307019916429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3460679472925538013277619 5191019209388307019916429)
  ·
    refine ⟨1946632203520615132468661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5191019209388307019916429 1946632203520615132468661)
    ·
      refine ⟨182496769080057668668937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1946632203520615132468661 182496769080057668668937)
      ·
        refine ⟨136872576810043251501703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182496769080057668668937 136872576810043251501703)
        ·
          refine ⟨205308865215064877252555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136872576810043251501703 205308865215064877252555)
          ·
            refine ⟨307963297822597315878833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205308865215064877252555 307963297822597315878833)
            ·
              refine ⟨230972473366947986909125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 307963297822597315878833 230972473366947986909125)
              ·
                refine ⟨43307338756302747545461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 230972473366947986909125 43307338756302747545461)
                ·
                  rfl

theorem cell19_142325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 4].length) (baseStart_142325 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_142325 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_142325 prefixEnd_142325 := by exact prefixLift 142325
  have htrace : WordTrace (prefixWord ++ tailWord_142325) baseStart_142325 baseEnd_142325 := by
    simpa [prefixWord, tailWord_142325, baseEnd_142325] using wordTrace_append hprefix tailTrace_142325
  have hstable : (prefixWord ++ tailWord_142325).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142325).length < 2 ^ (prefixWord ++ tailWord_142325).sum := by decide
  have hdescent : baseEnd_142325 < baseStart_142325 := by decide
  rcases family_descends (prefixWord ++ tailWord_142325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142369 : List Nat := [1, 2, 3, 2, 3, 8]
def baseStart_142369 : Nat := 118140960795 + 142369 * 2 ^ 59
def prefixEnd_142369 : Nat := 4983230072969 + 3 ^ 40 * 142369 * 2
def baseEnd_142369 : Nat := 4813414143213742507507

theorem tailTrace_142369 : CollatzResearch.WordTrace tailWord_142369 prefixEnd_142369 4813414143213742507507 := by
  unfold tailWord_142369
  simp only [CollatzResearch.WordTrace]
  refine ⟨5192624021228902534518161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3461749347485935023012107 5192624021228902534518161)
  ·
    refine ⟨3894468015921676900888621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5192624021228902534518161 3894468015921676900888621)
    ·
      refine ⟨1460425505970628837833233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3894468015921676900888621 1460425505970628837833233)
      ·
        refine ⟨1095319129477971628374925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1460425505970628837833233 1095319129477971628374925)
        ·
          refine ⟨410744673554239360640597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1095319129477971628374925 410744673554239360640597)
          ·
            refine ⟨4813414143213742507507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 410744673554239360640597 4813414143213742507507)
            ·
              rfl

theorem cell19_142369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 8].length) (baseStart_142369 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_142369 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_142369 prefixEnd_142369 := by exact prefixLift 142369
  have htrace : WordTrace (prefixWord ++ tailWord_142369) baseStart_142369 baseEnd_142369 := by
    simpa [prefixWord, tailWord_142369, baseEnd_142369] using wordTrace_append hprefix tailTrace_142369
  have hstable : (prefixWord ++ tailWord_142369).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142369).length < 2 ^ (prefixWord ++ tailWord_142369).sum := by decide
  have hdescent : baseEnd_142369 < baseStart_142369 := by decide
  rcases family_descends (prefixWord ++ tailWord_142369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142498 : List Nat := [3, 3, 1, 3, 2, 1, 2, 4]
def baseStart_142498 : Nat := 118140960795 + 142498 * 2 ^ 59
def prefixEnd_142498 : Nat := 4983230072969 + 3 ^ 40 * 142498 * 2
def baseEnd_142498 : Nat := 43359980032289605700545

theorem tailTrace_142498 : CollatzResearch.WordTrace tailWord_142498 prefixEnd_142498 43359980032289605700545 := by
  unfold tailWord_142498
  simp only [CollatzResearch.WordTrace]
  refine ⟨1299332259440389391491037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3464886025174371710642765 1299332259440389391491037)
  ·
    refine ⟨487249597290146021809139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1299332259440389391491037 487249597290146021809139)
    ·
      refine ⟨730874395935219032713709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 487249597290146021809139 730874395935219032713709)
      ·
        refine ⟨274077898475707137267641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 730874395935219032713709 274077898475707137267641)
        ·
          refine ⟨205558423856780352950731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 274077898475707137267641 205558423856780352950731)
          ·
            refine ⟨308337635785170529426097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205558423856780352950731 308337635785170529426097)
            ·
              refine ⟨231253226838877897069573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 308337635785170529426097 231253226838877897069573)
              ·
                refine ⟨43359980032289605700545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 231253226838877897069573 43359980032289605700545)
                ·
                  rfl

theorem cell19_142498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_142498 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_142498 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_142498 prefixEnd_142498 := by exact prefixLift 142498
  have htrace : WordTrace (prefixWord ++ tailWord_142498) baseStart_142498 baseEnd_142498 := by
    simpa [prefixWord, tailWord_142498, baseEnd_142498] using wordTrace_append hprefix tailTrace_142498
  have hstable : (prefixWord ++ tailWord_142498).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142498).length < 2 ^ (prefixWord ++ tailWord_142498).sum := by decide
  have hdescent : baseEnd_142498 < baseStart_142498 := by decide
  rcases family_descends (prefixWord ++ tailWord_142498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142500 : List Nat := [2, 3, 1, 2, 3, 2, 2, 4]
def baseStart_142500 : Nat := 118140960795 + 142500 * 2 ^ 59
def prefixEnd_142500 : Nat := 4983230072969 + 3 ^ 40 * 142500 * 2
def baseEnd_142500 : Nat := 43360588601954193656095

theorem tailTrace_142500 : CollatzResearch.WordTrace tailWord_142500 prefixEnd_142500 43360588601954193656095 := by
  unfold tailWord_142500
  simp only [CollatzResearch.WordTrace]
  refine ⟨2598700991877155953768477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3464934655836207938357969 2598700991877155953768477)
  ·
    refine ⟨974512871953933482663179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2598700991877155953768477 974512871953933482663179)
    ·
      refine ⟨1461769307930900223994769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 974512871953933482663179 1461769307930900223994769)
      ·
        refine ⟨1096326980948175167996077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1461769307930900223994769 1096326980948175167996077)
        ·
          refine ⟨411122617855565687998529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1096326980948175167996077 411122617855565687998529)
          ·
            refine ⟨308341963391674265998897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 411122617855565687998529 308341963391674265998897)
            ·
              refine ⟨231256472543755699499173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 308341963391674265998897 231256472543755699499173)
              ·
                refine ⟨43360588601954193656095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 231256472543755699499173 43360588601954193656095)
                ·
                  rfl

theorem cell19_142500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_142500 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_142500 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_142500 prefixEnd_142500 := by exact prefixLift 142500
  have htrace : WordTrace (prefixWord ++ tailWord_142500) baseStart_142500 baseEnd_142500 := by
    simpa [prefixWord, tailWord_142500, baseEnd_142500] using wordTrace_append hprefix tailTrace_142500
  have hstable : (prefixWord ++ tailWord_142500).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142500).length < 2 ^ (prefixWord ++ tailWord_142500).sum := by decide
  have hdescent : baseEnd_142500 < baseStart_142500 := by decide
  rcases family_descends (prefixWord ++ tailWord_142500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142521 : List Nat := [1, 2, 1, 4, 1, 3, 2, 5]
def baseStart_142521 : Nat := 118140960795 + 142521 * 2 ^ 59
def prefixEnd_142521 : Nat := 4983230072969 + 3 ^ 40 * 142521 * 2
def baseEnd_142521 : Nat := 43366978583432367189371

theorem tailTrace_142521 : CollatzResearch.WordTrace tailWord_142521 prefixEnd_142521 43366978583432367189371 := by
  unfold tailWord_142521
  simp only [CollatzResearch.WordTrace]
  refine ⟨5198167916678232494051417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3465445277785488329367611 5198167916678232494051417)
  ·
    refine ⟨3898625937508674370538563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5198167916678232494051417 3898625937508674370538563)
    ·
      refine ⟨5847938906263011555807845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3898625937508674370538563 5847938906263011555807845)
      ·
        refine ⟨1096488544924314666713971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5847938906263011555807845 1096488544924314666713971)
        ·
          refine ⟨1644732817386472000070957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1096488544924314666713971 1644732817386472000070957)
          ·
            refine ⟨616774806519927000026609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1644732817386472000070957 616774806519927000026609)
            ·
              refine ⟨462581104889945250019957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 616774806519927000026609 462581104889945250019957)
              ·
                refine ⟨43366978583432367189371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 462581104889945250019957 43366978583432367189371)
                ·
                  rfl

theorem cell19_142521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 5].length) (baseStart_142521 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_142521 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_142521 prefixEnd_142521 := by exact prefixLift 142521
  have htrace : WordTrace (prefixWord ++ tailWord_142521) baseStart_142521 baseEnd_142521 := by
    simpa [prefixWord, tailWord_142521, baseEnd_142521] using wordTrace_append hprefix tailTrace_142521
  have hstable : (prefixWord ++ tailWord_142521).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142521).length < 2 ^ (prefixWord ++ tailWord_142521).sum := by decide
  have hdescent : baseEnd_142521 < baseStart_142521 := by decide
  rcases family_descends (prefixWord ++ tailWord_142521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142534 : List Nat := [6, 1, 2, 2, 1, 7]
def baseStart_142534 : Nat := 118140960795 + 142534 * 2 ^ 59
def prefixEnd_142534 : Nat := 4983230072969 + 3 ^ 40 * 142534 * 2
def baseEnd_142534 : Nat := 4818992698472465433383

theorem tailTrace_142534 : CollatzResearch.WordTrace tailWord_142534 prefixEnd_142534 4818992698472465433383 := by
  unfold tailWord_142534
  simp only [CollatzResearch.WordTrace]
  refine ⟨162457564550972991071083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3465761377087423809516437 162457564550972991071083)
  ·
    refine ⟨243686346826459486606625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162457564550972991071083 243686346826459486606625)
    ·
      refine ⟨182764760119844614954969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243686346826459486606625 182764760119844614954969)
      ·
        refine ⟨137073570089883461216227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 182764760119844614954969 137073570089883461216227)
        ·
          refine ⟨205610355134825191824341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137073570089883461216227 205610355134825191824341)
          ·
            refine ⟨4818992698472465433383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 205610355134825191824341 4818992698472465433383)
            ·
              rfl

theorem cell19_142534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 7].length) (baseStart_142534 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_142534 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_142534 prefixEnd_142534 := by exact prefixLift 142534
  have htrace : WordTrace (prefixWord ++ tailWord_142534) baseStart_142534 baseEnd_142534 := by
    simpa [prefixWord, tailWord_142534, baseEnd_142534] using wordTrace_append hprefix tailTrace_142534
  have hstable : (prefixWord ++ tailWord_142534).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142534).length < 2 ^ (prefixWord ++ tailWord_142534).sum := by decide
  have hdescent : baseEnd_142534 < baseStart_142534 := by decide
  rcases family_descends (prefixWord ++ tailWord_142534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142559 : List Nat := [1, 1, 2, 3, 2, 1, 5, 4]
def baseStart_142559 : Nat := 118140960795 + 142559 * 2 ^ 59
def prefixEnd_142559 : Nat := 4983230072969 + 3 ^ 40 * 142559 * 2
def baseEnd_142559 : Nat := 43378541407059538344823

theorem tailTrace_142559 : CollatzResearch.WordTrace tailWord_142559 prefixEnd_142559 43378541407059538344823 := by
  unfold tailWord_142559
  simp only [CollatzResearch.WordTrace]
  refine ⟨5199553890540564983934731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3466369260360376655956487 5199553890540564983934731)
  ·
    refine ⟨7799330835810847475902097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5199553890540564983934731 7799330835810847475902097)
    ·
      refine ⟨5849498126858135606926573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7799330835810847475902097 5849498126858135606926573)
      ·
        refine ⟨2193561797571800852597465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5849498126858135606926573 2193561797571800852597465)
        ·
          refine ⟨1645171348178850639448099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2193561797571800852597465 1645171348178850639448099)
          ·
            refine ⟨2467757022268275959172149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1645171348178850639448099 2467757022268275959172149)
            ·
              refine ⟨231352220837650871172389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2467757022268275959172149 231352220837650871172389)
              ·
                refine ⟨43378541407059538344823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 231352220837650871172389 43378541407059538344823)
                ·
                  rfl

theorem cell19_142559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 4].length) (baseStart_142559 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_142559 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_142559 prefixEnd_142559 := by exact prefixLift 142559
  have htrace : WordTrace (prefixWord ++ tailWord_142559) baseStart_142559 baseEnd_142559 := by
    simpa [prefixWord, tailWord_142559, baseEnd_142559] using wordTrace_append hprefix tailTrace_142559
  have hstable : (prefixWord ++ tailWord_142559).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142559).length < 2 ^ (prefixWord ++ tailWord_142559).sum := by decide
  have hdescent : baseEnd_142559 < baseStart_142559 := by decide
  rcases family_descends (prefixWord ++ tailWord_142559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142673 : List Nat := [1, 2, 2, 1, 4, 1, 4, 4]
def baseStart_142673 : Nat := 118140960795 + 142673 * 2 ^ 59
def prefixEnd_142673 : Nat := 4983230072969 + 3 ^ 40 * 142673 * 2
def baseEnd_142673 : Nat := 43413229877941051811179

theorem tailTrace_142673 : CollatzResearch.WordTrace tailWord_142673 prefixEnd_142673 43413229877941051811179 := by
  unfold tailWord_142673
  simp only [CollatzResearch.WordTrace]
  refine ⟨5203711812127562453584673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3469141208085041635723115 5203711812127562453584673)
  ·
    refine ⟨3902783859095671840188505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5203711812127562453584673 3902783859095671840188505)
    ·
      refine ⟨2927087894321753880141379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3902783859095671840188505 2927087894321753880141379)
      ·
        refine ⟨4390631841482630820212069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2927087894321753880141379 4390631841482630820212069)
        ·
          refine ⟨823243470277993278789763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4390631841482630820212069 823243470277993278789763)
          ·
            refine ⟨1234865205416989918184645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 823243470277993278789763 1234865205416989918184645)
            ·
              refine ⟨231537226015685609659621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1234865205416989918184645 231537226015685609659621)
              ·
                refine ⟨43413229877941051811179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 231537226015685609659621 43413229877941051811179)
                ·
                  rfl

theorem cell19_142673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 4].length) (baseStart_142673 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_142673 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_142673 prefixEnd_142673 := by exact prefixLift 142673
  have htrace : WordTrace (prefixWord ++ tailWord_142673) baseStart_142673 baseEnd_142673 := by
    simpa [prefixWord, tailWord_142673, baseEnd_142673] using wordTrace_append hprefix tailTrace_142673
  have hstable : (prefixWord ++ tailWord_142673).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142673).length < 2 ^ (prefixWord ++ tailWord_142673).sum := by decide
  have hdescent : baseEnd_142673 < baseStart_142673 := by decide
  rcases family_descends (prefixWord ++ tailWord_142673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142692 : List Nat := [2, 3, 1, 1, 3, 2, 2, 5]
def baseStart_142692 : Nat := 118140960795 + 142692 * 2 ^ 59
def prefixEnd_142692 : Nat := 4983230072969 + 3 ^ 40 * 142692 * 2
def baseEnd_142692 : Nat := 43419011289754637388905

theorem tailTrace_142692 : CollatzResearch.WordTrace tailWord_142692 prefixEnd_142692 43419011289754637388905 := by
  unfold tailWord_142692
  simp only [CollatzResearch.WordTrace]
  refine ⟨2602202399529364349263165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3469603199372485799017553 2602202399529364349263165)
  ·
    refine ⟨975825899823511630973687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2602202399529364349263165 975825899823511630973687)
    ·
      refine ⟨1463738849735267446460531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 975825899823511630973687 1463738849735267446460531)
      ·
        refine ⟨2195608274602901169690797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1463738849735267446460531 2195608274602901169690797)
        ·
          refine ⟨823353102976087938634049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2195608274602901169690797 823353102976087938634049)
          ·
            refine ⟨617514827232065953975537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 823353102976087938634049 617514827232065953975537)
            ·
              refine ⟨463136120424049465481653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 617514827232065953975537 463136120424049465481653)
              ·
                refine ⟨43419011289754637388905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 463136120424049465481653 43419011289754637388905)
                ·
                  rfl

theorem cell19_142692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_142692 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_142692 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_142692 prefixEnd_142692 := by exact prefixLift 142692
  have htrace : WordTrace (prefixWord ++ tailWord_142692) baseStart_142692 baseEnd_142692 := by
    simpa [prefixWord, tailWord_142692, baseEnd_142692] using wordTrace_append hprefix tailTrace_142692
  have hstable : (prefixWord ++ tailWord_142692).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142692).length < 2 ^ (prefixWord ++ tailWord_142692).sum := by decide
  have hdescent : baseEnd_142692 < baseStart_142692 := by decide
  rcases family_descends (prefixWord ++ tailWord_142692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142709 : List Nat := [1, 3, 4, 1, 4, 6]
def baseStart_142709 : Nat := 118140960795 + 142709 * 2 ^ 59
def prefixEnd_142709 : Nat := 4983230072969 + 3 ^ 40 * 142709 * 2
def baseEnd_142709 : Nat := 4824909347989292779009

theorem tailTrace_142709 : CollatzResearch.WordTrace tailWord_142709 prefixEnd_142709 4824909347989292779009 := by
  unfold tailWord_142709
  simp only [CollatzResearch.WordTrace]
  refine ⟨5205024839997140601895181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3470016559998093734596787 5205024839997140601895181)
  ·
    refine ⟨1951884314998927725710693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5205024839997140601895181 1951884314998927725710693)
    ·
      refine ⟨365978309062298948570755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1951884314998927725710693 365978309062298948570755)
      ·
        refine ⟨548967463593448422856133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365978309062298948570755 548967463593448422856133)
        ·
          refine ⟨102931399423771579285525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 548967463593448422856133 102931399423771579285525)
          ·
            refine ⟨4824909347989292779009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 102931399423771579285525 4824909347989292779009)
            ·
              rfl

theorem cell19_142709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 6].length) (baseStart_142709 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_142709 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_142709 prefixEnd_142709 := by exact prefixLift 142709
  have htrace : WordTrace (prefixWord ++ tailWord_142709) baseStart_142709 baseEnd_142709 := by
    simpa [prefixWord, tailWord_142709, baseEnd_142709] using wordTrace_append hprefix tailTrace_142709
  have hstable : (prefixWord ++ tailWord_142709).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142709).length < 2 ^ (prefixWord ++ tailWord_142709).sum := by decide
  have hdescent : baseEnd_142709 < baseStart_142709 := by decide
  rcases family_descends (prefixWord ++ tailWord_142709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142728 : List Nat := [2, 1, 3, 3, 1, 4, 1, 4]
def baseStart_142728 : Nat := 118140960795 + 142728 * 2 ^ 59
def prefixEnd_142728 : Nat := 4983230072969 + 3 ^ 40 * 142728 * 2
def baseEnd_142728 : Nat := 43429965543717220588807

theorem tailTrace_142728 : CollatzResearch.WordTrace tailWord_142728 prefixEnd_142728 43429965543717220588807 := by
  unfold tailWord_142728
  simp only [CollatzResearch.WordTrace]
  refine ⟨2602858913464153423418419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3470478551285537897891225 2602858913464153423418419)
  ·
    refine ⟨3904288370196230135127629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2602858913464153423418419 3904288370196230135127629)
    ·
      refine ⟨1464108138823586300672861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3904288370196230135127629 1464108138823586300672861)
      ·
        refine ⟨549040552058844862752323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1464108138823586300672861 549040552058844862752323)
        ·
          refine ⟨823560828088267294128485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 549040552058844862752323 823560828088267294128485)
          ·
            refine ⟨154417655266550117649091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 823560828088267294128485 154417655266550117649091)
            ·
              refine ⟨231626482899825176473637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154417655266550117649091 231626482899825176473637)
              ·
                refine ⟨43429965543717220588807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 231626482899825176473637 43429965543717220588807)
                ·
                  rfl

theorem cell19_142728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 4].length) (baseStart_142728 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_142728 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_142728 prefixEnd_142728 := by exact prefixLift 142728
  have htrace : WordTrace (prefixWord ++ tailWord_142728) baseStart_142728 baseEnd_142728 := by
    simpa [prefixWord, tailWord_142728, baseEnd_142728] using wordTrace_append hprefix tailTrace_142728
  have hstable : (prefixWord ++ tailWord_142728).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142728).length < 2 ^ (prefixWord ++ tailWord_142728).sum := by decide
  have hdescent : baseEnd_142728 < baseStart_142728 := by decide
  rcases family_descends (prefixWord ++ tailWord_142728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142804 : List Nat := [2, 4, 1, 2, 3, 1, 1, 5]
def baseStart_142804 : Nat := 118140960795 + 142804 * 2 ^ 59
def prefixEnd_142804 : Nat := 4983230072969 + 3 ^ 40 * 142804 * 2
def baseEnd_142804 : Nat := 43453091190971562899711

theorem tailTrace_142804 : CollatzResearch.WordTrace tailWord_142804 prefixEnd_142804 43453091190971562899711 := by
  unfold tailWord_142804
  simp only [CollatzResearch.WordTrace]
  refine ⟨2604244887326485913301733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3472326516435314551068977 2604244887326485913301733)
  ·
    refine ⟨488295916373716108744075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2604244887326485913301733 488295916373716108744075)
    ·
      refine ⟨732443874560574163116113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 488295916373716108744075 732443874560574163116113)
      ·
        refine ⟨549332905920430622337085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 732443874560574163116113 549332905920430622337085)
        ·
          refine ⟨205999839720161483376407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 549332905920430622337085 205999839720161483376407)
          ·
            refine ⟨308999759580242225064611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 205999839720161483376407 308999759580242225064611)
            ·
              refine ⟨463499639370363337596917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308999759580242225064611 463499639370363337596917)
              ·
                refine ⟨43453091190971562899711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 463499639370363337596917 43453091190971562899711)
                ·
                  rfl

theorem cell19_142804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 5].length) (baseStart_142804 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_142804 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_142804 prefixEnd_142804 := by exact prefixLift 142804
  have htrace : WordTrace (prefixWord ++ tailWord_142804) baseStart_142804 baseEnd_142804 := by
    simpa [prefixWord, tailWord_142804, baseEnd_142804] using wordTrace_append hprefix tailTrace_142804
  have hstable : (prefixWord ++ tailWord_142804).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142804).length < 2 ^ (prefixWord ++ tailWord_142804).sum := by decide
  have hdescent : baseEnd_142804 < baseStart_142804 := by decide
  rcases family_descends (prefixWord ++ tailWord_142804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142865 : List Nat := [1, 2, 2, 1, 1, 2, 3, 7]
def baseStart_142865 : Nat := 118140960795 + 142865 * 2 ^ 59
def prefixEnd_142865 : Nat := 4983230072969 + 3 ^ 40 * 142865 * 2
def baseEnd_142865 : Nat := 43471652565741495543989

theorem tailTrace_142865 : CollatzResearch.WordTrace tailWord_142865 prefixEnd_142865 43471652565741495543989 := by
  unfold tailWord_142865
  simp only [CollatzResearch.WordTrace]
  refine ⟨5210714627431979244574049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3473809751621319496382699 5210714627431979244574049)
  ·
    refine ⟨3908035970573984433430537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5210714627431979244574049 3908035970573984433430537)
    ·
      refine ⟨2931026977930488325072903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3908035970573984433430537 2931026977930488325072903)
      ·
        refine ⟨4396540466895732487609355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2931026977930488325072903 4396540466895732487609355)
        ·
          refine ⟨6594810700343598731414033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4396540466895732487609355 6594810700343598731414033)
          ·
            refine ⟨4946108025257699048560525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6594810700343598731414033 4946108025257699048560525)
            ·
              refine ⟨1854790509471637143210197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4946108025257699048560525 1854790509471637143210197)
              ·
                refine ⟨43471652565741495543989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1854790509471637143210197 43471652565741495543989)
                ·
                  rfl

theorem cell19_142865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 7].length) (baseStart_142865 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_142865 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_142865 prefixEnd_142865 := by exact prefixLift 142865
  have htrace : WordTrace (prefixWord ++ tailWord_142865) baseStart_142865 baseEnd_142865 := by
    simpa [prefixWord, tailWord_142865, baseEnd_142865] using wordTrace_append hprefix tailTrace_142865
  have hstable : (prefixWord ++ tailWord_142865).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142865).length < 2 ^ (prefixWord ++ tailWord_142865).sum := by decide
  have hdescent : baseEnd_142865 < baseStart_142865 := by decide
  rcases family_descends (prefixWord ++ tailWord_142865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142878 : List Nat := [4, 3, 3, 1, 8]
def baseStart_142878 : Nat := 118140960795 + 142878 * 2 ^ 59
def prefixEnd_142878 : Nat := 4983230072969 + 3 ^ 40 * 142878 * 2
def baseEnd_142878 : Nat := 1610207713650419157595

theorem tailTrace_142878 : CollatzResearch.WordTrace tailWord_142878 prefixEnd_142878 1610207713650419157595 := by
  unfold tailWord_142878
  simp only [CollatzResearch.WordTrace]
  refine ⟨651398597048110308099661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3474125850923254976531525 651398597048110308099661)
  ·
    refine ⟨244274473893041365537373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 651398597048110308099661 244274473893041365537373)
    ·
      refine ⟨91602927709890512076515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244274473893041365537373 91602927709890512076515)
      ·
        refine ⟨137404391564835768114773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91602927709890512076515 137404391564835768114773)
        ·
          refine ⟨1610207713650419157595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 137404391564835768114773 1610207713650419157595)
          ·
            rfl

theorem cell19_142878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 8].length) (baseStart_142878 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_142878 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_142878 prefixEnd_142878 := by exact prefixLift 142878
  have htrace : WordTrace (prefixWord ++ tailWord_142878) baseStart_142878 baseEnd_142878 := by
    simpa [prefixWord, tailWord_142878, baseEnd_142878] using wordTrace_append hprefix tailTrace_142878
  have hstable : (prefixWord ++ tailWord_142878).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142878).length < 2 ^ (prefixWord ++ tailWord_142878).sum := by decide
  have hdescent : baseEnd_142878 < baseStart_142878 := by decide
  rcases family_descends (prefixWord ++ tailWord_142878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142884 : List Nat := [2, 3, 1, 13]
def baseStart_142884 : Nat := 118140960795 + 142884 * 2 ^ 59
def prefixEnd_142884 : Nat := 4983230072969 + 3 ^ 40 * 142884 * 2
def baseEnd_142884 : Nat := 536758444167346680515

theorem tailTrace_142884 : CollatzResearch.WordTrace tailWord_142884 prefixEnd_142884 536758444167346680515 := by
  unfold tailWord_142884
  simp only [CollatzResearch.WordTrace]
  refine ⟨2605703807181572744757853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3474271742908763659677137 2605703807181572744757853)
  ·
    refine ⟨977138927693089779284195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2605703807181572744757853 977138927693089779284195)
    ·
      refine ⟨1465708391539634668926293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 977138927693089779284195 1465708391539634668926293)
      ·
        refine ⟨536758444167346680515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 1465708391539634668926293 536758444167346680515)
        ·
          rfl

theorem cell19_142884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 13].length) (baseStart_142884 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_142884 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_142884 prefixEnd_142884 := by exact prefixLift 142884
  have htrace : WordTrace (prefixWord ++ tailWord_142884) baseStart_142884 baseEnd_142884 := by
    simpa [prefixWord, tailWord_142884, baseEnd_142884] using wordTrace_append hprefix tailTrace_142884
  have hstable : (prefixWord ++ tailWord_142884).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142884).length < 2 ^ (prefixWord ++ tailWord_142884).sum := by decide
  have hdescent : baseEnd_142884 < baseStart_142884 := by decide
  rcases family_descends (prefixWord ++ tailWord_142884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142901 : List Nat := [1, 3, 3, 1, 1, 3, 3, 4]
def baseStart_142901 : Nat := 118140960795 + 142901 * 2 ^ 59
def prefixEnd_142901 : Nat := 4983230072969 + 3 ^ 40 * 142901 * 2
def baseEnd_142901 : Nat := 43482606819704078743891

theorem tailTrace_142901 : CollatzResearch.WordTrace tailWord_142901 prefixEnd_142901 43482606819704078743891 := by
  unfold tailWord_142901
  simp only [CollatzResearch.WordTrace]
  refine ⟨5212027655301557392884557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3474685103534371595256371 5212027655301557392884557)
  ·
    refine ⟨1954510370738084022331709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5212027655301557392884557 1954510370738084022331709)
    ·
      refine ⟨732941389026781508374391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1954510370738084022331709 732941389026781508374391)
      ·
        refine ⟨1099412083540172262561587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 732941389026781508374391 1099412083540172262561587)
        ·
          refine ⟨1649118125310258393842381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1099412083540172262561587 1649118125310258393842381)
          ·
            refine ⟨618419296991346897690893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1649118125310258393842381 618419296991346897690893)
            ·
              refine ⟨231907236371755086634085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 618419296991346897690893 231907236371755086634085)
              ·
                refine ⟨43482606819704078743891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 231907236371755086634085 43482606819704078743891)
                ·
                  rfl

theorem cell19_142901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 4].length) (baseStart_142901 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_142901 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_142901 prefixEnd_142901 := by exact prefixLift 142901
  have htrace : WordTrace (prefixWord ++ tailWord_142901) baseStart_142901 baseEnd_142901 := by
    simpa [prefixWord, tailWord_142901, baseEnd_142901] using wordTrace_append hprefix tailTrace_142901
  have hstable : (prefixWord ++ tailWord_142901).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142901).length < 2 ^ (prefixWord ++ tailWord_142901).sum := by decide
  have hdescent : baseEnd_142901 < baseStart_142901 := by decide
  rcases family_descends (prefixWord ++ tailWord_142901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142977 : List Nat := [1, 2, 4, 2, 1, 3, 1, 5]
def baseStart_142977 : Nat := 118140960795 + 142977 * 2 ^ 59
def prefixEnd_142977 : Nat := 4983230072969 + 3 ^ 40 * 142977 * 2
def baseEnd_142977 : Nat := 43505732466958421054795

theorem tailTrace_142977 : CollatzResearch.WordTrace tailWord_142977 prefixEnd_142977 43505732466958421054795 := by
  unfold tailWord_142977
  simp only [CollatzResearch.WordTrace]
  refine ⟨5214799603026222372651185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3476533068684148248434123 5214799603026222372651185)
  ·
    refine ⟨3911099702269666779488389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5214799603026222372651185 3911099702269666779488389)
    ·
      refine ⟨733331194175562521154073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3911099702269666779488389 733331194175562521154073)
      ·
        refine ⟨549998395631671890865555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 733331194175562521154073 549998395631671890865555)
        ·
          refine ⟨824997593447507836298333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 549998395631671890865555 824997593447507836298333)
          ·
            refine ⟨309374097542815438611875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 824997593447507836298333 309374097542815438611875)
            ·
              refine ⟨464061146314223157917813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309374097542815438611875 464061146314223157917813)
              ·
                refine ⟨43505732466958421054795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 464061146314223157917813 43505732466958421054795)
                ·
                  rfl

theorem cell19_142977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 5].length) (baseStart_142977 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_142977 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_142977 prefixEnd_142977 := by exact prefixLift 142977
  have htrace : WordTrace (prefixWord ++ tailWord_142977) baseStart_142977 baseEnd_142977 := by
    simpa [prefixWord, tailWord_142977, baseEnd_142977] using wordTrace_append hprefix tailTrace_142977
  have hstable : (prefixWord ++ tailWord_142977).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142977).length < 2 ^ (prefixWord ++ tailWord_142977).sum := by decide
  have hdescent : baseEnd_142977 < baseStart_142977 := by decide
  rcases family_descends (prefixWord ++ tailWord_142977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142994 : List Nat := [3, 2, 3, 1, 3, 2, 5]
def baseStart_142994 : Nat := 118140960795 + 142994 * 2 ^ 59
def prefixEnd_142994 : Nat := 4983230072969 + 3 ^ 40 * 142994 * 2
def baseEnd_142994 : Nat := 14503635103035806225657

theorem tailTrace_142994 : CollatzResearch.WordTrace tailWord_142994 prefixEnd_142994 14503635103035806225657 := by
  unfold tailWord_142994
  simp only [CollatzResearch.WordTrace]
  refine ⟨1303854910991158569005009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3476946429309756184013357 1303854910991158569005009)
  ·
    refine ⟨977891183243368926753757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1303854910991158569005009 977891183243368926753757)
    ·
      refine ⟨366709193716263347532659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 977891183243368926753757 366709193716263347532659)
      ·
        refine ⟨550063790574395021298989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366709193716263347532659 550063790574395021298989)
        ·
          refine ⟨206273921465398132987121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 550063790574395021298989 206273921465398132987121)
          ·
            refine ⟨154705441099048599740341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206273921465398132987121 154705441099048599740341)
            ·
              refine ⟨14503635103035806225657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 154705441099048599740341 14503635103035806225657)
              ·
                rfl

theorem cell19_142994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 5].length) (baseStart_142994 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_142994 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_142994 prefixEnd_142994 := by exact prefixLift 142994
  have htrace : WordTrace (prefixWord ++ tailWord_142994) baseStart_142994 baseEnd_142994 := by
    simpa [prefixWord, tailWord_142994, baseEnd_142994] using wordTrace_append hprefix tailTrace_142994
  have hstable : (prefixWord ++ tailWord_142994).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142994).length < 2 ^ (prefixWord ++ tailWord_142994).sum := by decide
  have hdescent : baseEnd_142994 < baseStart_142994 := by decide
  rcases family_descends (prefixWord ++ tailWord_142994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143068 : List Nat := [2, 2, 5, 1, 2, 2, 1, 4]
def baseStart_143068 : Nat := 118140960795 + 143068 * 2 ^ 59
def prefixEnd_143068 : Nat := 4983230072969 + 3 ^ 40 * 143068 * 2
def baseEnd_143068 : Nat := 43533422386697173032325

theorem tailTrace_143068 : CollatzResearch.WordTrace tailWord_143068 prefixEnd_143068 43533422386697173032325 := by
  unfold tailWord_143068
  simp only [CollatzResearch.WordTrace]
  refine ⟨2609059322848272457106929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3478745763797696609475905 2609059322848272457106929)
  ·
    refine ⟨1956794492136204342830197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2609059322848272457106929 1956794492136204342830197)
    ·
      refine ⟨183449483637769157140331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1956794492136204342830197 183449483637769157140331)
      ·
        refine ⟨275174225456653735710497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183449483637769157140331 275174225456653735710497)
        ·
          refine ⟨206380669092490301782873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275174225456653735710497 206380669092490301782873)
          ·
            refine ⟨154785501819367726337155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206380669092490301782873 154785501819367726337155)
            ·
              refine ⟨232178252729051589505733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154785501819367726337155 232178252729051589505733)
              ·
                refine ⟨43533422386697173032325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 232178252729051589505733 43533422386697173032325)
                ·
                  rfl

theorem cell19_143068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 4].length) (baseStart_143068 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_143068 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_143068 prefixEnd_143068 := by exact prefixLift 143068
  have htrace : WordTrace (prefixWord ++ tailWord_143068) baseStart_143068 baseEnd_143068 := by
    simpa [prefixWord, tailWord_143068, baseEnd_143068] using wordTrace_append hprefix tailTrace_143068
  have hstable : (prefixWord ++ tailWord_143068).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143068).length < 2 ^ (prefixWord ++ tailWord_143068).sum := by decide
  have hdescent : baseEnd_143068 < baseStart_143068 := by decide
  rcases family_descends (prefixWord ++ tailWord_143068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143112 : List Nat := [2, 1, 3, 2, 2, 1, 8]
def baseStart_143112 : Nat := 118140960795 + 143112 * 2 ^ 59
def prefixEnd_143112 : Nat := 4983230072969 + 3 ^ 40 * 143112 * 2
def baseEnd_143112 : Nat := 14515603639772702684809

theorem tailTrace_143112 : CollatzResearch.WordTrace tailWord_143112 prefixEnd_143112 14515603639772702684809 := by
  unfold tailWord_143112
  simp only [CollatzResearch.WordTrace]
  refine ⟨2609861728768570214407795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3479815638358093619210393 2609861728768570214407795)
  ·
    refine ⟨3914792593152855321611693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2609861728768570214407795 3914792593152855321611693)
    ·
      refine ⟨1468047222432320745604385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3914792593152855321611693 1468047222432320745604385)
      ·
        refine ⟨1101035416824240559203289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1468047222432320745604385 1101035416824240559203289)
        ·
          refine ⟨825776562618180419402467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1101035416824240559203289 825776562618180419402467)
          ·
            refine ⟨1238664843927270629103701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 825776562618180419402467 1238664843927270629103701)
            ·
              refine ⟨14515603639772702684809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1238664843927270629103701 14515603639772702684809)
              ·
                rfl

theorem cell19_143112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 8].length) (baseStart_143112 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_143112 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_143112 prefixEnd_143112 := by exact prefixLift 143112
  have htrace : WordTrace (prefixWord ++ tailWord_143112) baseStart_143112 baseEnd_143112 := by
    simpa [prefixWord, tailWord_143112, baseEnd_143112] using wordTrace_append hprefix tailTrace_143112
  have hstable : (prefixWord ++ tailWord_143112).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143112).length < 2 ^ (prefixWord ++ tailWord_143112).sum := by decide
  have hdescent : baseEnd_143112 < baseStart_143112 := by decide
  rcases family_descends (prefixWord ++ tailWord_143112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143148 : List Nat := [2, 2, 1, 1, 1, 5, 4, 3]
def baseStart_143148 : Nat := 118140960795 + 143148 * 2 ^ 59
def prefixEnd_143148 : Nat := 4983230072969 + 3 ^ 40 * 143148 * 2
def baseEnd_143148 : Nat := 43557765173280691254329

theorem tailTrace_143148 : CollatzResearch.WordTrace tailWord_143148 prefixEnd_143148 43557765173280691254329 := by
  unfold tailWord_143148
  simp only [CollatzResearch.WordTrace]
  refine ⟨2610518242703359288563049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3480690990271145718084065 2610518242703359288563049)
  ·
    refine ⟨1957888682027519466422287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2610518242703359288563049 1957888682027519466422287)
    ·
      refine ⟨2936833023041279199633431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1957888682027519466422287 2936833023041279199633431)
      ·
        refine ⟨4405249534561918799450147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2936833023041279199633431 4405249534561918799450147)
        ·
          refine ⟨6607874301842878199175221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4405249534561918799450147 6607874301842878199175221)
          ·
            refine ⟨619488215797769831172677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6607874301842878199175221 619488215797769831172677)
            ·
              refine ⟨116154040462081843344877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 619488215797769831172677 116154040462081843344877)
              ·
                refine ⟨43557765173280691254329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116154040462081843344877 43557765173280691254329)
                ·
                  rfl

theorem cell19_143148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 3].length) (baseStart_143148 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_143148 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_143148 prefixEnd_143148 := by exact prefixLift 143148
  have htrace : WordTrace (prefixWord ++ tailWord_143148) baseStart_143148 baseEnd_143148 := by
    simpa [prefixWord, tailWord_143148, baseEnd_143148] using wordTrace_append hprefix tailTrace_143148
  have hstable : (prefixWord ++ tailWord_143148).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143148).length < 2 ^ (prefixWord ++ tailWord_143148).sum := by decide
  have hdescent : baseEnd_143148 < baseStart_143148 := by decide
  rcases family_descends (prefixWord ++ tailWord_143148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143167 : List Nat := [1, 1, 2, 2, 6, 2, 5]
def baseStart_143167 : Nat := 118140960795 + 143167 * 2 ^ 59
def prefixEnd_143167 : Nat := 4983230072969 + 3 ^ 40 * 143167 * 2
def baseEnd_143167 : Nat := 14521182195031425610685

theorem tailTrace_143167 : CollatzResearch.WordTrace tailWord_143167 prefixEnd_143167 14521182195031425610685 := by
  unfold tailWord_143167
  simp only [CollatzResearch.WordTrace]
  refine ⟨5221729472337884822067755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3481152981558589881378503 5221729472337884822067755)
  ·
    refine ⟨7832594208506827233101633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5221729472337884822067755 7832594208506827233101633)
    ·
      refine ⟨5874445656380120424826225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7832594208506827233101633 5874445656380120424826225)
      ·
        refine ⟨4405834242285090318619669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5874445656380120424826225 4405834242285090318619669)
        ·
          refine ⟨206523480107113608685297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4405834242285090318619669 206523480107113608685297)
          ·
            refine ⟨154892610080335206513973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206523480107113608685297 154892610080335206513973)
            ·
              refine ⟨14521182195031425610685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 154892610080335206513973 14521182195031425610685)
              ·
                rfl

theorem cell19_143167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 5].length) (baseStart_143167 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_143167 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_143167 prefixEnd_143167 := by exact prefixLift 143167
  have htrace : WordTrace (prefixWord ++ tailWord_143167) baseStart_143167 baseEnd_143167 := by
    simpa [prefixWord, tailWord_143167, baseEnd_143167] using wordTrace_append hprefix tailTrace_143167
  have hstable : (prefixWord ++ tailWord_143167).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143167).length < 2 ^ (prefixWord ++ tailWord_143167).sum := by decide
  have hdescent : baseEnd_143167 < baseStart_143167 := by decide
  rcases family_descends (prefixWord ++ tailWord_143167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143186 : List Nat := [3, 2, 2, 1, 1, 4, 2, 4]
def baseStart_143186 : Nat := 118140960795 + 143186 * 2 ^ 59
def prefixEnd_143186 : Nat := 4983230072969 + 3 ^ 40 * 143186 * 2
def baseEnd_143186 : Nat := 43569327996907862409781

theorem tailTrace_143186 : CollatzResearch.WordTrace tailWord_143186 prefixEnd_143186 43569327996907862409781 := by
  unfold tailWord_143186
  simp only [CollatzResearch.WordTrace]
  refine ⟨1305605614817262766752353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3481614972846034044672941 1305605614817262766752353)
  ·
    refine ⟨979204211112947075064265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1305605614817262766752353 979204211112947075064265)
    ·
      refine ⟨734403158334710306298199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 979204211112947075064265 734403158334710306298199)
      ·
        refine ⟨1101604737502065459447299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 734403158334710306298199 1101604737502065459447299)
        ·
          refine ⟨1652407106253098189170949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1101604737502065459447299 1652407106253098189170949)
          ·
            refine ⟨309826332422455910469553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1652407106253098189170949 309826332422455910469553)
            ·
              refine ⟨232369749316841932852165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 309826332422455910469553 232369749316841932852165)
              ·
                refine ⟨43569327996907862409781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 232369749316841932852165 43569327996907862409781)
                ·
                  rfl

theorem cell19_143186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_143186 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_143186 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_143186 prefixEnd_143186 := by exact prefixLift 143186
  have htrace : WordTrace (prefixWord ++ tailWord_143186) baseStart_143186 baseEnd_143186 := by
    simpa [prefixWord, tailWord_143186, baseEnd_143186] using wordTrace_append hprefix tailTrace_143186
  have hstable : (prefixWord ++ tailWord_143186).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143186).length < 2 ^ (prefixWord ++ tailWord_143186).sum := by decide
  have hdescent : baseEnd_143186 < baseStart_143186 := by decide
  rcases family_descends (prefixWord ++ tailWord_143186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143207 : List Nat := [1, 1, 5, 1, 2, 1, 1, 7]
def baseStart_143207 : Nat := 118140960795 + 143207 * 2 ^ 59
def prefixEnd_143207 : Nat := 4983230072969 + 3 ^ 40 * 143207 * 2
def baseEnd_143207 : Nat := 43575717978386035943057

theorem tailTrace_143207 : CollatzResearch.WordTrace tailWord_143207 prefixEnd_143207 43575717978386035943057 := by
  unfold tailWord_143207
  simp only [CollatzResearch.WordTrace]
  refine ⟨5223188392192971653523875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3482125594795314435682583 5223188392192971653523875)
  ·
    refine ⟨7834782588289457480285813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5223188392192971653523875 7834782588289457480285813)
    ·
      refine ⟨734510867652136638776795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7834782588289457480285813 734510867652136638776795)
      ·
        refine ⟨1101766301478204958165193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 734510867652136638776795 1101766301478204958165193)
        ·
          refine ⟨826324726108653718623895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1101766301478204958165193 826324726108653718623895)
          ·
            refine ⟨1239487089162980577935843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 826324726108653718623895 1239487089162980577935843)
            ·
              refine ⟨1859230633744470866903765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1239487089162980577935843 1859230633744470866903765)
              ·
                refine ⟨43575717978386035943057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1859230633744470866903765 43575717978386035943057)
                ·
                  rfl

theorem cell19_143207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 7].length) (baseStart_143207 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_143207 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_143207 prefixEnd_143207 := by exact prefixLift 143207
  have htrace : WordTrace (prefixWord ++ tailWord_143207) baseStart_143207 baseEnd_143207 := by
    simpa [prefixWord, tailWord_143207, baseEnd_143207] using wordTrace_append hprefix tailTrace_143207
  have hstable : (prefixWord ++ tailWord_143207).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143207).length < 2 ^ (prefixWord ++ tailWord_143207).sum := by decide
  have hdescent : baseEnd_143207 < baseStart_143207 := by decide
  rcases family_descends (prefixWord ++ tailWord_143207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143222 : List Nat := [5, 1, 1, 3, 3, 6]
def baseStart_143222 : Nat := 118140960795 + 143222 * 2 ^ 59
def prefixEnd_143222 : Nat := 4983230072969 + 3 ^ 40 * 143222 * 2
def baseEnd_143222 : Nat := 4842253583430049512187

theorem tailTrace_143222 : CollatzResearch.WordTrace tailWord_143222 prefixEnd_143222 4842253583430049512187 := by
  unfold tailWord_143222
  simp only [CollatzResearch.WordTrace]
  refine ⟨326483467946164325957495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3482490324759086143546613 326483467946164325957495)
  ·
    refine ⟨489725201919246488936243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 326483467946164325957495 489725201919246488936243)
    ·
      refine ⟨734587802878869733404365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 489725201919246488936243 734587802878869733404365)
      ·
        refine ⟨275470426079576150026637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 734587802878869733404365 275470426079576150026637)
        ·
          refine ⟨103301409779841056259989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 275470426079576150026637 103301409779841056259989)
          ·
            refine ⟨4842253583430049512187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 103301409779841056259989 4842253583430049512187)
            ·
              rfl

theorem cell19_143222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 6].length) (baseStart_143222 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_143222 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_143222 prefixEnd_143222 := by exact prefixLift 143222
  have htrace : WordTrace (prefixWord ++ tailWord_143222) baseStart_143222 baseEnd_143222 := by
    simpa [prefixWord, tailWord_143222, baseEnd_143222] using wordTrace_append hprefix tailTrace_143222
  have hstable : (prefixWord ++ tailWord_143222).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143222).length < 2 ^ (prefixWord ++ tailWord_143222).sum := by decide
  have hdescent : baseEnd_143222 < baseStart_143222 := by decide
  rcases family_descends (prefixWord ++ tailWord_143222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143260 : List Nat := [2, 2, 3, 3, 1, 2, 3, 3]
def baseStart_143260 : Nat := 118140960795 + 143260 * 2 ^ 59
def prefixEnd_143260 : Nat := 4983230072969 + 3 ^ 40 * 143260 * 2
def baseEnd_143260 : Nat := 43591845074497616765135

theorem tailTrace_143260 : CollatzResearch.WordTrace tailWord_143260 prefixEnd_143260 43591845074497616765135 := by
  unfold tailWord_143260
  simp only [CollatzResearch.WordTrace]
  refine ⟨2612560730500480852601617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3483414307333974470135489 2612560730500480852601617)
  ·
    refine ⟨1959420547875360639451213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2612560730500480852601617 1959420547875360639451213)
    ·
      refine ⟨734782705453260239794205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1959420547875360639451213 734782705453260239794205)
      ·
        refine ⟨275543514544972589922827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 734782705453260239794205 275543514544972589922827)
        ·
          refine ⟨413315271817458884884241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275543514544972589922827 413315271817458884884241)
          ·
            refine ⟨309986453863094163663181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 413315271817458884884241 309986453863094163663181)
            ·
              refine ⟨116244920198660311373693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 309986453863094163663181 116244920198660311373693)
              ·
                refine ⟨43591845074497616765135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116244920198660311373693 43591845074497616765135)
                ·
                  rfl

theorem cell19_143260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 3].length) (baseStart_143260 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_143260 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_143260 prefixEnd_143260 := by exact prefixLift 143260
  have htrace : WordTrace (prefixWord ++ tailWord_143260) baseStart_143260 baseEnd_143260 := by
    simpa [prefixWord, tailWord_143260, baseEnd_143260] using wordTrace_append hprefix tailTrace_143260
  have hstable : (prefixWord ++ tailWord_143260).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143260).length < 2 ^ (prefixWord ++ tailWord_143260).sum := by decide
  have hdescent : baseEnd_143260 < baseStart_143260 := by decide
  rcases family_descends (prefixWord ++ tailWord_143260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143317 : List Nat := [1, 3, 2, 3, 2, 3, 2, 3]
def baseStart_143317 : Nat := 118140960795 + 143317 * 2 ^ 59
def prefixEnd_143317 : Nat := 4983230072969 + 3 ^ 40 * 143317 * 2
def baseEnd_143317 : Nat := 43609189309938373498313

theorem tailTrace_143317 : CollatzResearch.WordTrace tailWord_143317 prefixEnd_143317 43609189309938373498313 := by
  unfold tailWord_143317
  simp only [CollatzResearch.WordTrace]
  refine ⟨5227200421794460440028205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3484800281196306960018803 5227200421794460440028205)
  ·
    refine ⟨1960200158172922665010577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5227200421794460440028205 1960200158172922665010577)
    ·
      refine ⟨1470150118629691998757933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1960200158172922665010577 1470150118629691998757933)
      ·
        refine ⟨551306294486134499534225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1470150118629691998757933 551306294486134499534225)
        ·
          refine ⟨413479720864600874650669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 551306294486134499534225 413479720864600874650669)
          ·
            refine ⟨155054895324225327994001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 413479720864600874650669 155054895324225327994001)
            ·
              refine ⟨116291171493168995995501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155054895324225327994001 116291171493168995995501)
              ·
                refine ⟨43609189309938373498313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116291171493168995995501 43609189309938373498313)
                ·
                  rfl

theorem cell19_143317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 3].length) (baseStart_143317 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_143317 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_143317 prefixEnd_143317 := by exact prefixLift 143317
  have htrace : WordTrace (prefixWord ++ tailWord_143317) baseStart_143317 baseEnd_143317 := by
    simpa [prefixWord, tailWord_143317, baseEnd_143317] using wordTrace_append hprefix tailTrace_143317
  have hstable : (prefixWord ++ tailWord_143317).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143317).length < 2 ^ (prefixWord ++ tailWord_143317).sum := by decide
  have hdescent : baseEnd_143317 < baseStart_143317 := by decide
  rcases family_descends (prefixWord ++ tailWord_143317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143492 : List Nat := [2, 3, 2, 1, 2, 1, 3, 5]
def baseStart_143492 : Nat := 118140960795 + 143492 * 2 ^ 59
def prefixEnd_143492 : Nat := 4983230072969 + 3 ^ 40 * 143492 * 2
def baseEnd_143492 : Nat := 43662439155589819608947

theorem tailTrace_143492 : CollatzResearch.WordTrace tailWord_143492 prefixEnd_143492 43662439155589819608947 := by
  unfold tailWord_143492
  simp only [CollatzResearch.WordTrace]
  refine ⟨2616791598080232663824365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3489055464106976885099153 2616791598080232663824365)
  ·
    refine ⟨981296849280087248934137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2616791598080232663824365 981296849280087248934137)
    ·
      refine ⟨735972636960065436700603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 981296849280087248934137 735972636960065436700603)
      ·
        refine ⟨1103958955440098155050905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 735972636960065436700603 1103958955440098155050905)
        ·
          refine ⟨827969216580073616288179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1103958955440098155050905 827969216580073616288179)
          ·
            refine ⟨1241953824870110424432269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 827969216580073616288179 1241953824870110424432269)
            ·
              refine ⟨465732684326291409162101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1241953824870110424432269 465732684326291409162101)
              ·
                refine ⟨43662439155589819608947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 465732684326291409162101 43662439155589819608947)
                ·
                  rfl

theorem cell19_143492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_143492 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_143492 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_143492 prefixEnd_143492 := by exact prefixLift 143492
  have htrace : WordTrace (prefixWord ++ tailWord_143492) baseStart_143492 baseEnd_143492 := by
    simpa [prefixWord, tailWord_143492, baseEnd_143492] using wordTrace_append hprefix tailTrace_143492
  have hstable : (prefixWord ++ tailWord_143492).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143492).length < 2 ^ (prefixWord ++ tailWord_143492).sum := by decide
  have hdescent : baseEnd_143492 < baseStart_143492 := by decide
  rcases family_descends (prefixWord ++ tailWord_143492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143606 : List Nat := [5, 1, 1, 1, 1, 1, 2, 7]
def baseStart_143606 : Nat := 118140960795 + 143606 * 2 ^ 59
def prefixEnd_143606 : Nat := 4983230072969 + 3 ^ 40 * 143606 * 2
def baseEnd_143606 : Nat := 43697127626471333075303

theorem tailTrace_143606 : CollatzResearch.WordTrace tailWord_143606 prefixEnd_143606 43697127626471333075303 := by
  unfold tailWord_143606
  simp only [CollatzResearch.WordTrace]
  refine ⟨327358819859216424831167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3491827411831641864865781 327358819859216424831167)
  ·
    refine ⟨491038229788824637246751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 327358819859216424831167 491038229788824637246751)
    ·
      refine ⟨736557344683236955870127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 491038229788824637246751 736557344683236955870127)
      ·
        refine ⟨1104836017024855433805191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 736557344683236955870127 1104836017024855433805191)
        ·
          refine ⟨1657254025537283150707787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1104836017024855433805191 1657254025537283150707787)
          ·
            refine ⟨2485881038305924726061681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1657254025537283150707787 2485881038305924726061681)
            ·
              refine ⟨1864410778729443544546261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2485881038305924726061681 1864410778729443544546261)
              ·
                refine ⟨43697127626471333075303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1864410778729443544546261 43697127626471333075303)
                ·
                  rfl

theorem cell19_143606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_143606 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_143606 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_143606 prefixEnd_143606 := by exact prefixLift 143606
  have htrace : WordTrace (prefixWord ++ tailWord_143606) baseStart_143606 baseEnd_143606 := by
    simpa [prefixWord, tailWord_143606, baseEnd_143606] using wordTrace_append hprefix tailTrace_143606
  have hstable : (prefixWord ++ tailWord_143606).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143606).length < 2 ^ (prefixWord ++ tailWord_143606).sum := by decide
  have hdescent : baseEnd_143606 < baseStart_143606 := by decide
  rcases family_descends (prefixWord ++ tailWord_143606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143608 : List Nat := [2, 1, 2, 1, 1, 2, 1, 9]
def baseStart_143608 : Nat := 118140960795 + 143608 * 2 ^ 59
def prefixEnd_143608 : Nat := 4983230072969 + 3 ^ 40 * 143608 * 2
def baseEnd_143608 : Nat := 43697736196135921030853

theorem tailTrace_143608 : CollatzResearch.WordTrace tailWord_143608 prefixEnd_143608 43697736196135921030853 := by
  unfold tailWord_143608
  simp only [CollatzResearch.WordTrace]
  refine ⟨2618907031870108569435739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3491876042493478092580985 2618907031870108569435739)
  ·
    refine ⟨3928360547805162854153609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2618907031870108569435739 3928360547805162854153609)
    ·
      refine ⟨2946270410853872140615207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3928360547805162854153609 2946270410853872140615207)
      ·
        refine ⟨4419405616280808210922811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2946270410853872140615207 4419405616280808210922811)
        ·
          refine ⟨6629108424421212316384217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4419405616280808210922811 6629108424421212316384217)
          ·
            refine ⟨4971831318315909237288163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6629108424421212316384217 4971831318315909237288163)
            ·
              refine ⟨7457746977473863855932245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4971831318315909237288163 7457746977473863855932245)
              ·
                refine ⟨43697736196135921030853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7457746977473863855932245 43697736196135921030853)
                ·
                  rfl

theorem cell19_143608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_143608 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_143608 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_143608 prefixEnd_143608 := by exact prefixLift 143608
  have htrace : WordTrace (prefixWord ++ tailWord_143608) baseStart_143608 baseEnd_143608 := by
    simpa [prefixWord, tailWord_143608, baseEnd_143608] using wordTrace_append hprefix tailTrace_143608
  have hstable : (prefixWord ++ tailWord_143608).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143608).length < 2 ^ (prefixWord ++ tailWord_143608).sum := by decide
  have hdescent : baseEnd_143608 < baseStart_143608 := by decide
  rcases family_descends (prefixWord ++ tailWord_143608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143623 : List Nat := [1, 1, 4, 5, 1, 1, 6]
def baseStart_143623 : Nat := 118140960795 + 143623 * 2 ^ 59
def prefixEnd_143623 : Nat := 4983230072969 + 3 ^ 40 * 143623 * 2
def baseEnd_143623 : Nat := 14567433489540110232493

theorem tailTrace_143623 : CollatzResearch.WordTrace tailWord_143623 prefixEnd_143623 14567433489540110232493 := by
  unfold tailWord_143623
  simp only [CollatzResearch.WordTrace]
  refine ⟨5238361158685874700667523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3492240772457249800445015 5238361158685874700667523)
  ·
    refine ⟨7857541738028812051001285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5238361158685874700667523 7857541738028812051001285)
    ·
      refine ⟨1473289075880402259562741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7857541738028812051001285 1473289075880402259562741)
      ·
        refine ⟨138120850863787711834007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1473289075880402259562741 138120850863787711834007)
        ·
          refine ⟨207181276295681567751011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138120850863787711834007 207181276295681567751011)
          ·
            refine ⟨310771914443522351626517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207181276295681567751011 310771914443522351626517)
            ·
              refine ⟨14567433489540110232493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 310771914443522351626517 14567433489540110232493)
              ·
                rfl

theorem cell19_143623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 6].length) (baseStart_143623 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_143623 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_143623 prefixEnd_143623 := by exact prefixLift 143623
  have htrace : WordTrace (prefixWord ++ tailWord_143623) baseStart_143623 baseEnd_143623 := by
    simpa [prefixWord, tailWord_143623, baseEnd_143623] using wordTrace_append hprefix tailTrace_143623
  have hstable : (prefixWord ++ tailWord_143623).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143623).length < 2 ^ (prefixWord ++ tailWord_143623).sum := by decide
  have hdescent : baseEnd_143623 < baseStart_143623 := by decide
  rcases family_descends (prefixWord ++ tailWord_143623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143627 : List Nat := [1, 1, 1, 1, 5, 2, 8]
def baseStart_143627 : Nat := 118140960795 + 143627 * 2 ^ 59
def prefixEnd_143627 : Nat := 4983230072969 + 3 ^ 40 * 143627 * 2
def baseEnd_143627 : Nat := 14567839202649835536193

theorem tailTrace_143627 : CollatzResearch.WordTrace tailWord_143627 prefixEnd_143627 14567839202649835536193 := by
  unfold tailWord_143627
  simp only [CollatzResearch.WordTrace]
  refine ⟨5238507050671383383813135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3492338033780922255875423 5238507050671383383813135)
  ·
    refine ⟨7857760576007075075719703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5238507050671383383813135 7857760576007075075719703)
    ·
      refine ⟨11786640864010612613579555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7857760576007075075719703 11786640864010612613579555)
      ·
        refine ⟨17679961296015918920369333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11786640864010612613579555 17679961296015918920369333)
        ·
          refine ⟨1657496371501492398784625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17679961296015918920369333 1657496371501492398784625)
          ·
            refine ⟨1243122278626119299088469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1657496371501492398784625 1243122278626119299088469)
            ·
              refine ⟨14567839202649835536193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1243122278626119299088469 14567839202649835536193)
              ·
                rfl

theorem cell19_143627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 8].length) (baseStart_143627 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_143627 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_143627 prefixEnd_143627 := by exact prefixLift 143627
  have htrace : WordTrace (prefixWord ++ tailWord_143627) baseStart_143627 baseEnd_143627 := by
    simpa [prefixWord, tailWord_143627, baseEnd_143627] using wordTrace_append hprefix tailTrace_143627
  have hstable : (prefixWord ++ tailWord_143627).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143627).length < 2 ^ (prefixWord ++ tailWord_143627).sum := by decide
  have hdescent : baseEnd_143627 < baseStart_143627 := by decide
  rcases family_descends (prefixWord ++ tailWord_143627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143655 : List Nat := [1, 1, 8, 1, 1, 2, 2, 3]
def baseStart_143655 : Nat := 118140960795 + 143655 * 2 ^ 59
def prefixEnd_143655 : Nat := 4983230072969 + 3 ^ 40 * 143655 * 2
def baseEnd_143655 : Nat := 43712037583253737986281

theorem tailTrace_143655 : CollatzResearch.WordTrace tailWord_143655 prefixEnd_143655 43712037583253737986281 := by
  unfold tailWord_143655
  simp only [CollatzResearch.WordTrace]
  refine ⟨5239528294569944165832419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3493018863046629443888279 5239528294569944165832419)
  ·
    refine ⟨7859292441854916248748629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5239528294569944165832419 7859292441854916248748629)
    ·
      refine ⟨92101083302987299790023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 7859292441854916248748629 92101083302987299790023)
      ·
        refine ⟨138151624954480949685035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92101083302987299790023 138151624954480949685035)
        ·
          refine ⟨207227437431721424527553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138151624954480949685035 207227437431721424527553)
          ·
            refine ⟨155420578073791068395665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207227437431721424527553 155420578073791068395665)
            ·
              refine ⟨116565433555343301296749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155420578073791068395665 116565433555343301296749)
              ·
                refine ⟨43712037583253737986281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116565433555343301296749 43712037583253737986281)
                ·
                  rfl

theorem cell19_143655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 3].length) (baseStart_143655 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_143655 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_143655 prefixEnd_143655 := by exact prefixLift 143655
  have htrace : WordTrace (prefixWord ++ tailWord_143655) baseStart_143655 baseEnd_143655 := by
    simpa [prefixWord, tailWord_143655, baseEnd_143655] using wordTrace_append hprefix tailTrace_143655
  have hstable : (prefixWord ++ tailWord_143655).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143655).length < 2 ^ (prefixWord ++ tailWord_143655).sum := by decide
  have hdescent : baseEnd_143655 < baseStart_143655 := by decide
  rcases family_descends (prefixWord ++ tailWord_143655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143663 : List Nat := [1, 1, 2, 1, 2, 1, 8, 3]
def baseStart_143663 : Nat := 118140960795 + 143663 * 2 ^ 59
def prefixEnd_143663 : Nat := 4983230072969 + 3 ^ 40 * 143663 * 2
def baseEnd_143663 : Nat := 43714471861912089808481

theorem tailTrace_143663 : CollatzResearch.WordTrace tailWord_143663 prefixEnd_143663 43714471861912089808481 := by
  unfold tailWord_143663
  simp only [CollatzResearch.WordTrace]
  refine ⟨5239820078540961532123643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3493213385693974354749095 5239820078540961532123643)
  ·
    refine ⟨7859730117811442298185465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5239820078540961532123643 7859730117811442298185465)
    ·
      refine ⟨5894797588358581723639099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7859730117811442298185465 5894797588358581723639099)
      ·
        refine ⟨8842196382537872585458649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5894797588358581723639099 8842196382537872585458649)
        ·
          refine ⟨6631647286903404439093987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8842196382537872585458649 6631647286903404439093987)
          ·
            refine ⟨9947470930355106658640981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6631647286903404439093987 9947470930355106658640981)
            ·
              refine ⟨116571924965098906155949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 9947470930355106658640981 116571924965098906155949)
              ·
                refine ⟨43714471861912089808481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116571924965098906155949 43714471861912089808481)
                ·
                  rfl

theorem cell19_143663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 3].length) (baseStart_143663 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_143663 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_143663 prefixEnd_143663 := by exact prefixLift 143663
  have htrace : WordTrace (prefixWord ++ tailWord_143663) baseStart_143663 baseEnd_143663 := by
    simpa [prefixWord, tailWord_143663, baseEnd_143663] using wordTrace_append hprefix tailTrace_143663
  have hstable : (prefixWord ++ tailWord_143663).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143663).length < 2 ^ (prefixWord ++ tailWord_143663).sum := by decide
  have hdescent : baseEnd_143663 < baseStart_143663 := by decide
  rcases family_descends (prefixWord ++ tailWord_143663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143720 : List Nat := [2, 1, 4, 2, 2, 1, 2, 5]
def baseStart_143720 : Nat := 118140960795 + 143720 * 2 ^ 59
def prefixEnd_143720 : Nat := 4983230072969 + 3 ^ 40 * 143720 * 2
def baseEnd_143720 : Nat := 43731816097352846541659

theorem tailTrace_143720 : CollatzResearch.WordTrace tailWord_143720 prefixEnd_143720 43731816097352846541659 := by
  unfold tailWord_143720
  simp only [CollatzResearch.WordTrace]
  refine ⟨2620949519667230133474307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3494599359556306844632409 2620949519667230133474307)
  ·
    refine ⟨3931424279500845200211461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2620949519667230133474307 3931424279500845200211461)
    ·
      refine ⟨737142052406408475039649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3931424279500845200211461 737142052406408475039649)
      ·
        refine ⟨552856539304806356279737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 737142052406408475039649 552856539304806356279737)
        ·
          refine ⟨414642404478604767209803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 552856539304806356279737 414642404478604767209803)
          ·
            refine ⟨621963606717907150814705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 414642404478604767209803 621963606717907150814705)
            ·
              refine ⟨466472705038430363111029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 621963606717907150814705 466472705038430363111029)
              ·
                refine ⟨43731816097352846541659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 466472705038430363111029 43731816097352846541659)
                ·
                  rfl

theorem cell19_143720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_143720 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_143720 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_143720 prefixEnd_143720 := by exact prefixLift 143720
  have htrace : WordTrace (prefixWord ++ tailWord_143720) baseStart_143720 baseEnd_143720 := by
    simpa [prefixWord, tailWord_143720, baseEnd_143720] using wordTrace_append hprefix tailTrace_143720
  have hstable : (prefixWord ++ tailWord_143720).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143720).length < 2 ^ (prefixWord ++ tailWord_143720).sum := by decide
  have hdescent : baseEnd_143720 < baseStart_143720 := by decide
  rcases family_descends (prefixWord ++ tailWord_143720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143741 : List Nat := [1, 4, 1, 1, 2, 10]
def baseStart_143741 : Nat := 118140960795 + 143741 * 2 ^ 59
def prefixEnd_143741 : Nat := 4983230072969 + 3 ^ 40 * 143741 * 2
def baseEnd_143741 : Nat := 4859800675425668897215

theorem tailTrace_143741 : CollatzResearch.WordTrace tailWord_143741 prefixEnd_143741 4859800675425668897215 := by
  unfold tailWord_143741
  simp only [CollatzResearch.WordTrace]
  refine ⟨5242664972258380853463077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3495109981505587235642051 5242664972258380853463077)
  ·
    refine ⟨982999682298446410024327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5242664972258380853463077 982999682298446410024327)
    ·
      refine ⟨1474499523447669615036491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 982999682298446410024327 1474499523447669615036491)
      ·
        refine ⟨2211749285171504422554737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1474499523447669615036491 2211749285171504422554737)
        ·
          refine ⟨1658811963878628316916053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2211749285171504422554737 1658811963878628316916053)
          ·
            refine ⟨4859800675425668897215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1658811963878628316916053 4859800675425668897215)
            ·
              rfl

theorem cell19_143741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 10].length) (baseStart_143741 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_143741 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_143741 prefixEnd_143741 := by exact prefixLift 143741
  have htrace : WordTrace (prefixWord ++ tailWord_143741) baseStart_143741 baseEnd_143741 := by
    simpa [prefixWord, tailWord_143741, baseEnd_143741] using wordTrace_append hprefix tailTrace_143741
  have hstable : (prefixWord ++ tailWord_143741).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143741).length < 2 ^ (prefixWord ++ tailWord_143741).sum := by decide
  have hdescent : baseEnd_143741 < baseStart_143741 := by decide
  rcases family_descends (prefixWord ++ tailWord_143741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143754 : List Nat := [3, 1, 2, 5, 1, 2, 1, 4]
def baseStart_143754 : Nat := 118140960795 + 143754 * 2 ^ 59
def prefixEnd_143754 : Nat := 4983230072969 + 3 ^ 40 * 143754 * 2
def baseEnd_143754 : Nat := 43742161781650841786011

theorem tailTrace_143754 : CollatzResearch.WordTrace tailWord_143754 prefixEnd_143754 43742161781650841786011 := by
  unfold tailWord_143754
  simp only [CollatzResearch.WordTrace]
  refine ⟨1310784780302821018421579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3495426080807522715790877 1310784780302821018421579)
  ·
    refine ⟨1966177170454231527632369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1310784780302821018421579 1966177170454231527632369)
    ·
      refine ⟨1474632877840673645724277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1966177170454231527632369 1474632877840673645724277)
      ·
        refine ⟨138246832297563154286651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1474632877840673645724277 138246832297563154286651)
        ·
          refine ⟨207370248446344731429977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138246832297563154286651 207370248446344731429977)
          ·
            refine ⟨155527686334758548572483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207370248446344731429977 155527686334758548572483)
            ·
              refine ⟨233291529502137822858725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155527686334758548572483 233291529502137822858725)
              ·
                refine ⟨43742161781650841786011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 233291529502137822858725 43742161781650841786011)
                ·
                  rfl

theorem cell19_143754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_143754 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_143754 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_143754 prefixEnd_143754 := by exact prefixLift 143754
  have htrace : WordTrace (prefixWord ++ tailWord_143754) baseStart_143754 baseEnd_143754 := by
    simpa [prefixWord, tailWord_143754, baseEnd_143754] using wordTrace_append hprefix tailTrace_143754
  have hstable : (prefixWord ++ tailWord_143754).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143754).length < 2 ^ (prefixWord ++ tailWord_143754).sum := by decide
  have hdescent : baseEnd_143754 < baseStart_143754 := by decide
  rcases family_descends (prefixWord ++ tailWord_143754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143853 : List Nat := [1, 5, 1, 3, 1, 1, 7]
def baseStart_143853 : Nat := 118140960795 + 143853 * 2 ^ 59
def prefixEnd_143853 : Nat := 4983230072969 + 3 ^ 40 * 143853 * 2
def baseEnd_143853 : Nat := 14590761993349315195247

theorem tailTrace_143853 : CollatzResearch.WordTrace tailWord_143853 prefixEnd_143853 14590761993349315195247 := by
  unfold tailWord_143853
  simp only [CollatzResearch.WordTrace]
  refine ⟨5246749947852623981540213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3497833298568415987693475 5246749947852623981540213)
  ·
    refine ⟨491882807611183498269395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5246749947852623981540213 491882807611183498269395)
    ·
      refine ⟨737824211416775247404093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 491882807611183498269395 737824211416775247404093)
      ·
        refine ⟨276684079281290717776535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 737824211416775247404093 276684079281290717776535)
        ·
          refine ⟨415026118921936076664803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276684079281290717776535 415026118921936076664803)
          ·
            refine ⟨622539178382904114997205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415026118921936076664803 622539178382904114997205)
            ·
              refine ⟨14590761993349315195247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 622539178382904114997205 14590761993349315195247)
              ·
                rfl

theorem cell19_143853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 7].length) (baseStart_143853 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_143853 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_143853 prefixEnd_143853 := by exact prefixLift 143853
  have htrace : WordTrace (prefixWord ++ tailWord_143853) baseStart_143853 baseEnd_143853 := by
    simpa [prefixWord, tailWord_143853, baseEnd_143853] using wordTrace_append hprefix tailTrace_143853
  have hstable : (prefixWord ++ tailWord_143853).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143853).length < 2 ^ (prefixWord ++ tailWord_143853).sum := by decide
  have hdescent : baseEnd_143853 < baseStart_143853 := by decide
  rcases family_descends (prefixWord ++ tailWord_143853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143893 : List Nat := [1, 3, 2, 1, 3, 1, 1, 7]
def baseStart_143893 : Nat := 118140960795 + 143893 * 2 ^ 59
def prefixEnd_143893 : Nat := 4983230072969 + 3 ^ 40 * 143893 * 2
def baseEnd_143893 : Nat := 43784457373339704696743

theorem tailTrace_143893 : CollatzResearch.WordTrace tailWord_143893 prefixEnd_143893 43784457373339704696743 := by
  unfold tailWord_143893
  simp only [CollatzResearch.WordTrace]
  refine ⟨5248208867707710812996333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3498805911805140541997555 5248208867707710812996333)
  ·
    refine ⟨1968078325390391554873625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5248208867707710812996333 1968078325390391554873625)
    ·
      refine ⟨1476058744042793666155219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1968078325390391554873625 1476058744042793666155219)
      ·
        refine ⟨2214088116064190499232829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1476058744042793666155219 2214088116064190499232829)
        ·
          refine ⟨830283043524071437212311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2214088116064190499232829 830283043524071437212311)
          ·
            refine ⟨1245424565286107155818467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 830283043524071437212311 1245424565286107155818467)
            ·
              refine ⟨1868136847929160733727701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1245424565286107155818467 1868136847929160733727701)
              ·
                refine ⟨43784457373339704696743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1868136847929160733727701 43784457373339704696743)
                ·
                  rfl

theorem cell19_143893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 7].length) (baseStart_143893 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_143893 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_143893 prefixEnd_143893 := by exact prefixLift 143893
  have htrace : WordTrace (prefixWord ++ tailWord_143893) baseStart_143893 baseEnd_143893 := by
    simpa [prefixWord, tailWord_143893, baseEnd_143893] using wordTrace_append hprefix tailTrace_143893
  have hstable : (prefixWord ++ tailWord_143893).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143893).length < 2 ^ (prefixWord ++ tailWord_143893).sum := by decide
  have hdescent : baseEnd_143893 < baseStart_143893 := by decide
  rcases family_descends (prefixWord ++ tailWord_143893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143908 : List Nat := [2, 3, 1, 5, 2, 6]
def baseStart_143908 : Nat := 118140960795 + 143908 * 2 ^ 59
def prefixEnd_143908 : Nat := 4983230072969 + 3 ^ 40 * 143908 * 2
def baseEnd_143908 : Nat := 4865446849536012707041

theorem tailTrace_143908 : CollatzResearch.WordTrace tailWord_143908 prefixEnd_143908 4865446849536012707041 := by
  unfold tailWord_143908
  simp only [CollatzResearch.WordTrace]
  refine ⟨2624377981326684187396189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3499170641768912249861585 2624377981326684187396189)
  ·
    refine ⟨984141742997506570273571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2624377981326684187396189 984141742997506570273571)
    ·
      refine ⟨1476212614496259855410357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 984141742997506570273571 1476212614496259855410357)
      ·
        refine ⟨138394932609024361444721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1476212614496259855410357 138394932609024361444721)
        ·
          refine ⟨103796199456768271083541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138394932609024361444721 103796199456768271083541)
          ·
            refine ⟨4865446849536012707041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 103796199456768271083541 4865446849536012707041)
            ·
              rfl

theorem cell19_143908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 6].length) (baseStart_143908 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_143908 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_143908 prefixEnd_143908 := by exact prefixLift 143908
  have htrace : WordTrace (prefixWord ++ tailWord_143908) baseStart_143908 baseEnd_143908 := by
    simpa [prefixWord, tailWord_143908, baseEnd_143908] using wordTrace_append hprefix tailTrace_143908
  have hstable : (prefixWord ++ tailWord_143908).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143908).length < 2 ^ (prefixWord ++ tailWord_143908).sum := by decide
  have hdescent : baseEnd_143908 < baseStart_143908 := by decide
  rcases family_descends (prefixWord ++ tailWord_143908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143948 : List Nat := [2, 2, 1, 3, 1, 2, 5, 3]
def baseStart_143948 : Nat := 118140960795 + 143948 * 2 ^ 59
def prefixEnd_143948 : Nat := 4983230072969 + 3 ^ 40 * 143948 * 2
def baseEnd_143948 : Nat := 43801193039115873474371

theorem tailTrace_143948 : CollatzResearch.WordTrace tailWord_143948 prefixEnd_143948 43801193039115873474371 := by
  unfold tailWord_143948
  simp only [CollatzResearch.WordTrace]
  refine ⟨2625107441254227603124249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3500143255005636804165665 2625107441254227603124249)
  ·
    refine ⟨1968830580940670702343187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2625107441254227603124249 1968830580940670702343187)
    ·
      refine ⟨2953245871411006053514781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1968830580940670702343187 2953245871411006053514781)
      ·
        refine ⟨1107467201779127270068043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2953245871411006053514781 1107467201779127270068043)
        ·
          refine ⟨1661200802668690905102065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1107467201779127270068043 1661200802668690905102065)
          ·
            refine ⟨1245900602001518178826549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1661200802668690905102065 1245900602001518178826549)
            ·
              refine ⟨116803181437642329264989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1245900602001518178826549 116803181437642329264989)
              ·
                refine ⟨43801193039115873474371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116803181437642329264989 43801193039115873474371)
                ·
                  rfl

theorem cell19_143948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 3].length) (baseStart_143948 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_143948 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_143948 prefixEnd_143948 := by exact prefixLift 143948
  have htrace : WordTrace (prefixWord ++ tailWord_143948) baseStart_143948 baseEnd_143948 := by
    simpa [prefixWord, tailWord_143948, baseEnd_143948] using wordTrace_append hprefix tailTrace_143948
  have hstable : (prefixWord ++ tailWord_143948).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143948).length < 2 ^ (prefixWord ++ tailWord_143948).sum := by decide
  have hdescent : baseEnd_143948 < baseStart_143948 := by decide
  rcases family_descends (prefixWord ++ tailWord_143948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143950 : List Nat := [4, 1, 1, 1, 1, 2, 2, 7]
def baseStart_143950 : Nat := 118140960795 + 143950 * 2 ^ 59
def prefixEnd_143950 : Nat := 4983230072969 + 3 ^ 40 * 143950 * 2
def baseEnd_143950 : Nat := 43801801608780461429921

theorem tailTrace_143950 : CollatzResearch.WordTrace tailWord_143950 prefixEnd_143950 43801801608780461429921 := by
  unfold tailWord_143950
  simp only [CollatzResearch.WordTrace]
  refine ⟨656285978562651193477663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3500191885667473031880869 656285978562651193477663)
  ·
    refine ⟨984428967843976790216495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 656285978562651193477663 984428967843976790216495)
    ·
      refine ⟨1476643451765965185324743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 984428967843976790216495 1476643451765965185324743)
      ·
        refine ⟨2214965177648947777987115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1476643451765965185324743 2214965177648947777987115)
        ·
          refine ⟨3322447766473421666980673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2214965177648947777987115 3322447766473421666980673)
          ·
            refine ⟨2491835824855066250235505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3322447766473421666980673 2491835824855066250235505)
            ·
              refine ⟨1868876868641299687676629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2491835824855066250235505 1868876868641299687676629)
              ·
                refine ⟨43801801608780461429921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1868876868641299687676629 43801801608780461429921)
                ·
                  rfl

theorem cell19_143950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_143950 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_143950 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_143950 prefixEnd_143950 := by exact prefixLift 143950
  have htrace : WordTrace (prefixWord ++ tailWord_143950) baseStart_143950 baseEnd_143950 := by
    simpa [prefixWord, tailWord_143950, baseEnd_143950] using wordTrace_append hprefix tailTrace_143950
  have hstable : (prefixWord ++ tailWord_143950).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143950).length < 2 ^ (prefixWord ++ tailWord_143950).sum := by decide
  have hdescent : baseEnd_143950 < baseStart_143950 := by decide
  rcases family_descends (prefixWord ++ tailWord_143950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143969 : List Nat := [1, 2, 3, 1, 1, 5, 6]
def baseStart_143969 : Nat := 118140960795 + 143969 * 2 ^ 59
def prefixEnd_143969 : Nat := 4983230072969 + 3 ^ 40 * 143969 * 2
def baseEnd_143969 : Nat := 14602527673531349002549

theorem tailTrace_143969 : CollatzResearch.WordTrace tailWord_143969 prefixEnd_143969 14602527673531349002549 := by
  unfold tailWord_143969
  simp only [CollatzResearch.WordTrace]
  refine ⟨5250980815432375792762961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3500653876954917195175307 5250980815432375792762961)
  ·
    refine ⟨3938235611574281844572221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5250980815432375792762961 3938235611574281844572221)
    ·
      refine ⟨1476838354340355691714583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3938235611574281844572221 1476838354340355691714583)
      ·
        refine ⟨2215257531510533537571875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1476838354340355691714583 2215257531510533537571875)
        ·
          refine ⟨3322886297265800306357813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2215257531510533537571875 3322886297265800306357813)
          ·
            refine ⟨311520590368668778721045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3322886297265800306357813 311520590368668778721045)
            ·
              refine ⟨14602527673531349002549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 311520590368668778721045 14602527673531349002549)
              ·
                rfl

theorem cell19_143969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 6].length) (baseStart_143969 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_143969 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_143969 prefixEnd_143969 := by exact prefixLift 143969
  have htrace : WordTrace (prefixWord ++ tailWord_143969) baseStart_143969 baseEnd_143969 := by
    simpa [prefixWord, tailWord_143969, baseEnd_143969] using wordTrace_append hprefix tailTrace_143969
  have hstable : (prefixWord ++ tailWord_143969).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143969).length < 2 ^ (prefixWord ++ tailWord_143969).sum := by decide
  have hdescent : baseEnd_143969 < baseStart_143969 := by decide
  rcases family_descends (prefixWord ++ tailWord_143969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144005 : List Nat := [1, 3, 1, 1, 4, 2, 4, 3]
def baseStart_144005 : Nat := 118140960795 + 144005 * 2 ^ 59
def prefixEnd_144005 : Nat := 4983230072969 + 3 ^ 40 * 144005 * 2
def baseEnd_144005 : Nat := 43818537274556630207549

theorem tailTrace_144005 : CollatzResearch.WordTrace tailWord_144005 prefixEnd_144005 43818537274556630207549 := by
  unfold tailWord_144005
  simp only [CollatzResearch.WordTrace]
  refine ⟨5252293843301953941073469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3501529228867969294048979 5252293843301953941073469)
  ·
    refine ⟨1969610191238232727902551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5252293843301953941073469 1969610191238232727902551)
    ·
      refine ⟨2954415286857349091853827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1969610191238232727902551 2954415286857349091853827)
      ·
        refine ⟨4431622930286023637780741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2954415286857349091853827 4431622930286023637780741)
        ·
          refine ⟨830929299428629432083889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4431622930286023637780741 830929299428629432083889)
          ·
            refine ⟨623196974571472074062917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 830929299428629432083889 623196974571472074062917)
            ·
              refine ⟨116849432732151013886797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 623196974571472074062917 116849432732151013886797)
              ·
                refine ⟨43818537274556630207549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116849432732151013886797 43818537274556630207549)
                ·
                  rfl

theorem cell19_144005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 3].length) (baseStart_144005 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_144005 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_144005 prefixEnd_144005 := by exact prefixLift 144005
  have htrace : WordTrace (prefixWord ++ tailWord_144005) baseStart_144005 baseEnd_144005 := by
    simpa [prefixWord, tailWord_144005, baseEnd_144005] using wordTrace_append hprefix tailTrace_144005
  have hstable : (prefixWord ++ tailWord_144005).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144005).length < 2 ^ (prefixWord ++ tailWord_144005).sum := by decide
  have hdescent : baseEnd_144005 < baseStart_144005 := by decide
  rcases family_descends (prefixWord ++ tailWord_144005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144007 : List Nat := [1, 1, 4, 2, 1, 2, 3, 5]
def baseStart_144007 : Nat := 118140960795 + 144007 * 2 ^ 59
def prefixEnd_144007 : Nat := 4983230072969 + 3 ^ 40 * 144007 * 2
def baseEnd_144007 : Nat := 43819145844221218163099

theorem tailTrace_144007 : CollatzResearch.WordTrace tailWord_144007 prefixEnd_144007 43819145844221218163099 := by
  unfold tailWord_144007
  simp only [CollatzResearch.WordTrace]
  refine ⟨5252366789294708282646275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3501577859529805521764183 5252366789294708282646275)
  ·
    refine ⟨7878550183942062423969413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5252366789294708282646275 7878550183942062423969413)
    ·
      refine ⟨1477228159489136704494265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7878550183942062423969413 1477228159489136704494265)
      ·
        refine ⟨1107921119616852528370699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1477228159489136704494265 1107921119616852528370699)
        ·
          refine ⟨1661881679425278792556049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1107921119616852528370699 1661881679425278792556049)
          ·
            refine ⟨1246411259568959094417037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1661881679425278792556049 1246411259568959094417037)
            ·
              refine ⟨467404222338359660406389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1246411259568959094417037 467404222338359660406389)
              ·
                refine ⟨43819145844221218163099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 467404222338359660406389 43819145844221218163099)
                ·
                  rfl

theorem cell19_144007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 5].length) (baseStart_144007 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_144007 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_144007 prefixEnd_144007 := by exact prefixLift 144007
  have htrace : WordTrace (prefixWord ++ tailWord_144007) baseStart_144007 baseEnd_144007 := by
    simpa [prefixWord, tailWord_144007, baseEnd_144007] using wordTrace_append hprefix tailTrace_144007
  have hstable : (prefixWord ++ tailWord_144007).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144007).length < 2 ^ (prefixWord ++ tailWord_144007).sum := by decide
  have hdescent : baseEnd_144007 < baseStart_144007 := by decide
  rcases family_descends (prefixWord ++ tailWord_144007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144064 : List Nat := [2, 1, 1, 2, 4, 2, 2, 5]
def baseStart_144064 : Nat := 118140960795 + 144064 * 2 ^ 59
def prefixEnd_144064 : Nat := 4983230072969 + 3 ^ 40 * 144064 * 2
def baseEnd_144064 : Nat := 43836490079661974896277

theorem tailTrace_144064 : CollatzResearch.WordTrace tailWord_144064 prefixEnd_144064 43836490079661974896277 := by
  unfold tailWord_144064
  simp only [CollatzResearch.WordTrace]
  refine ⟨2627222875044103508735623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3502963833392138011647497 2627222875044103508735623)
  ·
    refine ⟨3940834312566155263103435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2627222875044103508735623 3940834312566155263103435)
    ·
      refine ⟨5911251468849232894655153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3940834312566155263103435 5911251468849232894655153)
      ·
        refine ⟨4433438601636924670991365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5911251468849232894655153 4433438601636924670991365)
        ·
          refine ⟨831269737806923375810881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4433438601636924670991365 831269737806923375810881)
          ·
            refine ⟨623452303355192531858161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 831269737806923375810881 623452303355192531858161)
            ·
              refine ⟨467589227516394398893621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 623452303355192531858161 467589227516394398893621)
              ·
                refine ⟨43836490079661974896277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 467589227516394398893621 43836490079661974896277)
                ·
                  rfl

theorem cell19_144064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_144064 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_144064 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_144064 prefixEnd_144064 := by exact prefixLift 144064
  have htrace : WordTrace (prefixWord ++ tailWord_144064) baseStart_144064 baseEnd_144064 := by
    simpa [prefixWord, tailWord_144064, baseEnd_144064] using wordTrace_append hprefix tailTrace_144064
  have hstable : (prefixWord ++ tailWord_144064).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144064).length < 2 ^ (prefixWord ++ tailWord_144064).sum := by decide
  have hdescent : baseEnd_144064 < baseStart_144064 := by decide
  rcases family_descends (prefixWord ++ tailWord_144064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144100 : List Nat := [2, 3, 1, 1, 1, 6, 1, 4]
def baseStart_144100 : Nat := 118140960795 + 144100 * 2 ^ 59
def prefixEnd_144100 : Nat := 4983230072969 + 3 ^ 40 * 144100 * 2
def baseEnd_144100 : Nat := 43847444333624558096179

theorem tailTrace_144100 : CollatzResearch.WordTrace tailWord_144100 prefixEnd_144100 43847444333624558096179 := by
  unfold tailWord_144100
  simp only [CollatzResearch.WordTrace]
  refine ⟨2627879388978892582890877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3503839185305190110521169 2627879388978892582890877)
  ·
    refine ⟨985454770867084718584079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2627879388978892582890877 985454770867084718584079)
    ·
      refine ⟨1478182156300627077876119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 985454770867084718584079 1478182156300627077876119)
      ·
        refine ⟨2217273234450940616814179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1478182156300627077876119 2217273234450940616814179)
        ·
          refine ⟨3325909851676410925221269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2217273234450940616814179 3325909851676410925221269)
          ·
            refine ⟨155902024297331762119747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3325909851676410925221269 155902024297331762119747)
            ·
              refine ⟨233853036445997643179621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155902024297331762119747 233853036445997643179621)
              ·
                refine ⟨43847444333624558096179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 233853036445997643179621 43847444333624558096179)
                ·
                  rfl

theorem cell19_144100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 4].length) (baseStart_144100 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_144100 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_144100 prefixEnd_144100 := by exact prefixLift 144100
  have htrace : WordTrace (prefixWord ++ tailWord_144100) baseStart_144100 baseEnd_144100 := by
    simpa [prefixWord, tailWord_144100, baseEnd_144100] using wordTrace_append hprefix tailTrace_144100
  have hstable : (prefixWord ++ tailWord_144100).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144100).length < 2 ^ (prefixWord ++ tailWord_144100).sum := by decide
  have hdescent : baseEnd_144100 < baseStart_144100 := by decide
  rcases family_descends (prefixWord ++ tailWord_144100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144170 : List Nat := [3, 1, 4, 3, 2, 1, 2, 3]
def baseStart_144170 : Nat := 118140960795 + 144170 * 2 ^ 59
def prefixEnd_144170 : Nat := 4983230072969 + 3 ^ 40 * 144170 * 2
def baseEnd_144170 : Nat := 43868744271885136540433

theorem tailTrace_144170 : CollatzResearch.WordTrace tailWord_144170 prefixEnd_144170 43868744271885136540433 := by
  unfold tailWord_144170
  simp only [CollatzResearch.WordTrace]
  refine ⟨1314577971926046780207491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3505541258469458080553309 1314577971926046780207491)
  ·
    refine ⟨1971866957889070170311237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1314577971926046780207491 1971866957889070170311237)
    ·
      refine ⟨369725054604200656933357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1971866957889070170311237 369725054604200656933357)
      ·
        refine ⟨138646895476575246350009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 369725054604200656933357 138646895476575246350009)
        ·
          refine ⟨103985171607431434762507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138646895476575246350009 103985171607431434762507)
          ·
            refine ⟨155977757411147152143761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103985171607431434762507 155977757411147152143761)
            ·
              refine ⟨116983318058360364107821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155977757411147152143761 116983318058360364107821)
              ·
                refine ⟨43868744271885136540433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116983318058360364107821 43868744271885136540433)
                ·
                  rfl

theorem cell19_144170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_144170 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_144170 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_144170 prefixEnd_144170 := by exact prefixLift 144170
  have htrace : WordTrace (prefixWord ++ tailWord_144170) baseStart_144170 baseEnd_144170 := by
    simpa [prefixWord, tailWord_144170, baseEnd_144170] using wordTrace_append hprefix tailTrace_144170
  have hstable : (prefixWord ++ tailWord_144170).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144170).length < 2 ^ (prefixWord ++ tailWord_144170).sum := by decide
  have hdescent : baseEnd_144170 < baseStart_144170 := by decide
  rcases family_descends (prefixWord ++ tailWord_144170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144174 : List Nat := [4, 1, 3, 2, 1, 1, 4, 3]
def baseStart_144174 : Nat := 118140960795 + 144174 * 2 ^ 59
def prefixEnd_144174 : Nat := 4983230072969 + 3 ^ 40 * 144174 * 2
def baseEnd_144174 : Nat := 43869961411214312451533

theorem tailTrace_144174 : CollatzResearch.WordTrace tailWord_144174 prefixEnd_144174 43869961411214312451533 := by
  unfold tailWord_144174
  simp only [CollatzResearch.WordTrace]
  refine ⟨657307222461211975496947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3505638519793130535983717 657307222461211975496947)
  ·
    refine ⟨985960833691817963245421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 657307222461211975496947 985960833691817963245421)
    ·
      refine ⟨369735312634431736217033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 985960833691817963245421 369735312634431736217033)
      ·
        refine ⟨277301484475823802162775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 369735312634431736217033 277301484475823802162775)
        ·
          refine ⟨415952226713735703244163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277301484475823802162775 415952226713735703244163)
          ·
            refine ⟨623928340070603554866245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415952226713735703244163 623928340070603554866245)
            ·
              refine ⟨116986563763238166537421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 623928340070603554866245 116986563763238166537421)
              ·
                refine ⟨43869961411214312451533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116986563763238166537421 43869961411214312451533)
                ·
                  rfl

theorem cell19_144174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_144174 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_144174 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_144174 prefixEnd_144174 := by exact prefixLift 144174
  have htrace : WordTrace (prefixWord ++ tailWord_144174) baseStart_144174 baseEnd_144174 := by
    simpa [prefixWord, tailWord_144174, baseEnd_144174] using wordTrace_append hprefix tailTrace_144174
  have hstable : (prefixWord ++ tailWord_144174).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144174).length < 2 ^ (prefixWord ++ tailWord_144174).sum := by decide
  have hdescent : baseEnd_144174 < baseStart_144174 := by decide
  rcases family_descends (prefixWord ++ tailWord_144174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144178 : List Nat := [3, 2, 1, 1, 3, 1, 3, 5]
def baseStart_144178 : Nat := 118140960795 + 144178 * 2 ^ 59
def prefixEnd_144178 : Nat := 4983230072969 + 3 ^ 40 * 144178 * 2
def baseEnd_144178 : Nat := 43871178550543488362633

theorem tailTrace_144178 : CollatzResearch.WordTrace tailWord_144178 prefixEnd_144178 43871178550543488362633 := by
  unfold tailWord_144178
  simp only [CollatzResearch.WordTrace]
  refine ⟨1314650917918801121780297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3505735781116802991414125 1314650917918801121780297)
  ·
    refine ⟨985988188439100841335223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1314650917918801121780297 985988188439100841335223)
    ·
      refine ⟨1478982282658651262002835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 985988188439100841335223 1478982282658651262002835)
      ·
        refine ⟨2218473423987976893004253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1478982282658651262002835 2218473423987976893004253)
        ·
          refine ⟨831927533995491334876595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2218473423987976893004253 831927533995491334876595)
          ·
            refine ⟨1247891300993237002314893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 831927533995491334876595 1247891300993237002314893)
            ·
              refine ⟨467959237872463875868085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1247891300993237002314893 467959237872463875868085)
              ·
                refine ⟨43871178550543488362633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 467959237872463875868085 43871178550543488362633)
                ·
                  rfl

theorem cell19_144178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_144178 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_144178 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_144178 prefixEnd_144178 := by exact prefixLift 144178
  have htrace : WordTrace (prefixWord ++ tailWord_144178) baseStart_144178 baseEnd_144178 := by
    simpa [prefixWord, tailWord_144178, baseEnd_144178] using wordTrace_append hprefix tailTrace_144178
  have hstable : (prefixWord ++ tailWord_144178).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144178).length < 2 ^ (prefixWord ++ tailWord_144178).sum := by decide
  have hdescent : baseEnd_144178 < baseStart_144178 := by decide
  rcases family_descends (prefixWord ++ tailWord_144178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144193 : List Nat := [1, 2, 5, 3, 1, 2, 5]
def baseStart_144193 : Nat := 118140960795 + 144193 * 2 ^ 59
def prefixEnd_144193 : Nat := 4983230072969 + 3 ^ 40 * 144193 * 2
def baseEnd_144193 : Nat := 14625247607675966009753

theorem tailTrace_144193 : CollatzResearch.WordTrace tailWord_144193 prefixEnd_144193 14625247607675966009753 := by
  unfold tailWord_144193
  simp only [CollatzResearch.WordTrace]
  refine ⟨5259150766620862048917233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3506100511080574699278155 5259150766620862048917233)
  ·
    refine ⟨3944363074965646536687925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5259150766620862048917233 3944363074965646536687925)
    ·
      refine ⟨369784038278029362814493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3944363074965646536687925 369784038278029362814493)
      ·
        refine ⟨138669014354261011055435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 369784038278029362814493 138669014354261011055435)
        ·
          refine ⟨208003521531391516583153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138669014354261011055435 208003521531391516583153)
          ·
            refine ⟨156002641148543637437365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208003521531391516583153 156002641148543637437365)
            ·
              refine ⟨14625247607675966009753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 156002641148543637437365 14625247607675966009753)
              ·
                rfl

theorem cell19_144193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 5].length) (baseStart_144193 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_144193 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_144193 prefixEnd_144193 := by exact prefixLift 144193
  have htrace : WordTrace (prefixWord ++ tailWord_144193) baseStart_144193 baseEnd_144193 := by
    simpa [prefixWord, tailWord_144193, baseEnd_144193] using wordTrace_append hprefix tailTrace_144193
  have hstable : (prefixWord ++ tailWord_144193).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144193).length < 2 ^ (prefixWord ++ tailWord_144193).sum := by decide
  have hdescent : baseEnd_144193 < baseStart_144193 := by decide
  rcases family_descends (prefixWord ++ tailWord_144193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144275 : List Nat := [1, 1, 1, 2, 1, 2, 1, 10]
def baseStart_144275 : Nat := 118140960795 + 144275 * 2 ^ 59
def prefixEnd_144275 : Nat := 4983230072969 + 3 ^ 40 * 144275 * 2
def baseEnd_144275 : Nat := 43900694179276004206813

theorem tailTrace_144275 : CollatzResearch.WordTrace tailWord_144275 prefixEnd_144275 43900694179276004206813 := by
  unfold tailWord_144275
  simp only [CollatzResearch.WordTrace]
  refine ⟨5262141552323790053402279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3508094368215860035601519 5262141552323790053402279)
  ·
    refine ⟨7893212328485685080103419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5262141552323790053402279 7893212328485685080103419)
    ·
      refine ⟨11839818492728527620155129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7893212328485685080103419 11839818492728527620155129)
      ·
        refine ⟨8879863869546395715116347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11839818492728527620155129 8879863869546395715116347)
        ·
          refine ⟨13319795804319593572674521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8879863869546395715116347 13319795804319593572674521)
          ·
            refine ⟨9989846853239695179505891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13319795804319593572674521 9989846853239695179505891)
            ·
              refine ⟨14984770279859542769258837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9989846853239695179505891 14984770279859542769258837)
              ·
                refine ⟨43900694179276004206813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 14984770279859542769258837 43900694179276004206813)
                ·
                  rfl

theorem cell19_144275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 10].length) (baseStart_144275 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_144275 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_144275 prefixEnd_144275 := by exact prefixLift 144275
  have htrace : WordTrace (prefixWord ++ tailWord_144275) baseStart_144275 baseEnd_144275 := by
    simpa [prefixWord, tailWord_144275, baseEnd_144275] using wordTrace_append hprefix tailTrace_144275
  have hstable : (prefixWord ++ tailWord_144275).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144275).length < 2 ^ (prefixWord ++ tailWord_144275).sum := by decide
  have hdescent : baseEnd_144275 < baseStart_144275 := by decide
  rcases family_descends (prefixWord ++ tailWord_144275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144366 : List Nat := [4, 1, 2, 1, 4, 2, 5]
def baseStart_144366 : Nat := 118140960795 + 144366 * 2 ^ 59
def prefixEnd_144366 : Nat := 4983230072969 + 3 ^ 40 * 144366 * 2
def baseEnd_144366 : Nat := 14642794699671585394781

theorem tailTrace_144366 : CollatzResearch.WordTrace tailWord_144366 prefixEnd_144366 14642794699671585394781 := by
  unfold tailWord_144366
  simp only [CollatzResearch.WordTrace]
  refine ⟨658182574374264074370619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3510307063329408396643301 658182574374264074370619)
  ·
    refine ⟨987273861561396111555929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 658182574374264074370619 987273861561396111555929)
    ·
      refine ⟨740455396171047083666947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 987273861561396111555929 740455396171047083666947)
      ·
        refine ⟨1110683094256570625500421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 740455396171047083666947 1110683094256570625500421)
        ·
          refine ⟨208253080173106992281329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1110683094256570625500421 208253080173106992281329)
          ·
            refine ⟨156189810129830244210997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208253080173106992281329 156189810129830244210997)
            ·
              refine ⟨14642794699671585394781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 156189810129830244210997 14642794699671585394781)
              ·
                rfl

theorem cell19_144366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 5].length) (baseStart_144366 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_144366 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_144366 prefixEnd_144366 := by exact prefixLift 144366
  have htrace : WordTrace (prefixWord ++ tailWord_144366) baseStart_144366 baseEnd_144366 := by
    simpa [prefixWord, tailWord_144366, baseEnd_144366] using wordTrace_append hprefix tailTrace_144366
  have hstable : (prefixWord ++ tailWord_144366).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144366).length < 2 ^ (prefixWord ++ tailWord_144366).sum := by decide
  have hdescent : baseEnd_144366 < baseStart_144366 := by decide
  rcases family_descends (prefixWord ++ tailWord_144366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144444 : List Nat := [2, 2, 2, 2, 2, 2, 3, 4]
def baseStart_144444 : Nat := 118140960795 + 144444 * 2 ^ 59
def prefixEnd_144444 : Nat := 4983230072969 + 3 ^ 40 * 144444 * 2
def baseEnd_144444 : Nat := 43952118315933686450797

theorem tailTrace_144444 : CollatzResearch.WordTrace tailWord_144444 prefixEnd_144444 43952118315933686450797 := by
  unfold tailWord_144444
  simp only [CollatzResearch.WordTrace]
  refine ⟨2634152744355765958152193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3512203659141021277536257 2634152744355765958152193)
  ·
    refine ⟨1975614558266824468614145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2634152744355765958152193 1975614558266824468614145)
    ·
      refine ⟨1481710918700118351460609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1975614558266824468614145 1481710918700118351460609)
      ·
        refine ⟨1111283189025088763595457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1481710918700118351460609 1111283189025088763595457)
        ·
          refine ⟨833462391768816572696593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1111283189025088763595457 833462391768816572696593)
          ·
            refine ⟨625096793826612429522445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 833462391768816572696593 625096793826612429522445)
            ·
              refine ⟨234411297684979661070917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 625096793826612429522445 234411297684979661070917)
              ·
                refine ⟨43952118315933686450797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 234411297684979661070917 43952118315933686450797)
                ·
                  rfl

theorem cell19_144444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_144444 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_144444 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_144444 prefixEnd_144444 := by exact prefixLift 144444
  have htrace : WordTrace (prefixWord ++ tailWord_144444) baseStart_144444 baseEnd_144444 := by
    simpa [prefixWord, tailWord_144444, baseEnd_144444] using wordTrace_append hprefix tailTrace_144444
  have hstable : (prefixWord ++ tailWord_144444).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144444).length < 2 ^ (prefixWord ++ tailWord_144444).sum := by decide
  have hdescent : baseEnd_144444 < baseStart_144444 := by decide
  rcases family_descends (prefixWord ++ tailWord_144444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144465 : List Nat := [1, 2, 2, 1, 3, 1, 2, 7]
def baseStart_144465 : Nat := 118140960795 + 144465 * 2 ^ 59
def prefixEnd_144465 : Nat := 4983230072969 + 3 ^ 40 * 144465 * 2
def baseEnd_144465 : Nat := 43958508297411859984073

theorem tailTrace_144465 : CollatzResearch.WordTrace tailWord_144465 prefixEnd_144465 43958508297411859984073 := by
  unfold tailWord_144465
  simp only [CollatzResearch.WordTrace]
  refine ⟨5269071421635452502818849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3512714281090301668545899 5269071421635452502818849)
  ·
    refine ⟨3951803566226589377114137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5269071421635452502818849 3951803566226589377114137)
    ·
      refine ⟨2963852674669942032835603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3951803566226589377114137 2963852674669942032835603)
      ·
        refine ⟨4445779012004913049253405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2963852674669942032835603 4445779012004913049253405)
        ·
          refine ⟨1667167129501842393470027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4445779012004913049253405 1667167129501842393470027)
          ·
            refine ⟨2500750694252763590205041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1667167129501842393470027 2500750694252763590205041)
            ·
              refine ⟨1875563020689572692653781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2500750694252763590205041 1875563020689572692653781)
              ·
                refine ⟨43958508297411859984073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1875563020689572692653781 43958508297411859984073)
                ·
                  rfl

theorem cell19_144465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 7].length) (baseStart_144465 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_144465 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_144465 prefixEnd_144465 := by exact prefixLift 144465
  have htrace : WordTrace (prefixWord ++ tailWord_144465) baseStart_144465 baseEnd_144465 := by
    simpa [prefixWord, tailWord_144465, baseEnd_144465] using wordTrace_append hprefix tailTrace_144465
  have hstable : (prefixWord ++ tailWord_144465).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144465).length < 2 ^ (prefixWord ++ tailWord_144465).sum := by decide
  have hdescent : baseEnd_144465 < baseStart_144465 := by decide
  rcases family_descends (prefixWord ++ tailWord_144465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144478 : List Nat := [4, 4, 1, 1, 1, 2, 6]
def baseStart_144478 : Nat := 118140960795 + 144478 * 2 ^ 59
def prefixEnd_144478 : Nat := 4983230072969 + 3 ^ 40 * 144478 * 2
def baseEnd_144478 : Nat := 14654154666743893898383

theorem tailTrace_144478 : CollatzResearch.WordTrace tailWord_144478 prefixEnd_144478 14654154666743893898383 := by
  unfold tailWord_144478
  simp only [CollatzResearch.WordTrace]
  refine ⟨658693196323544465380261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3513030380392237148694725 658693196323544465380261)
  ·
    refine ⟨123504974310664587258799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 658693196323544465380261 123504974310664587258799)
    ·
      refine ⟨185257461465996880888199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123504974310664587258799 185257461465996880888199)
      ·
        refine ⟨277886192198995321332299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185257461465996880888199 277886192198995321332299)
        ·
          refine ⟨416829288298492981998449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277886192198995321332299 416829288298492981998449)
          ·
            refine ⟨312621966223869736498837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 416829288298492981998449 312621966223869736498837)
            ·
              refine ⟨14654154666743893898383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 312621966223869736498837 14654154666743893898383)
              ·
                rfl

theorem cell19_144478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 6].length) (baseStart_144478 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_144478 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_144478 prefixEnd_144478 := by exact prefixLift 144478
  have htrace : WordTrace (prefixWord ++ tailWord_144478) baseStart_144478 baseEnd_144478 := by
    simpa [prefixWord, tailWord_144478, baseEnd_144478] using wordTrace_append hprefix tailTrace_144478
  have hstable : (prefixWord ++ tailWord_144478).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144478).length < 2 ^ (prefixWord ++ tailWord_144478).sum := by decide
  have hdescent : baseEnd_144478 < baseStart_144478 := by decide
  rcases family_descends (prefixWord ++ tailWord_144478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144503 : List Nat := [1, 1, 3, 1, 1, 4, 2, 6]
def baseStart_144503 : Nat := 118140960795 + 144503 * 2 ^ 59
def prefixEnd_144503 : Nat := 4983230072969 + 3 ^ 40 * 144503 * 2
def baseEnd_144503 : Nat := 43970071121039031139525

theorem tailTrace_144503 : CollatzResearch.WordTrace tailWord_144503 prefixEnd_144503 43970071121039031139525 := by
  unfold tailWord_144503
  simp only [CollatzResearch.WordTrace]
  refine ⟨5270457395497784992702163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3513638263665189995134775 5270457395497784992702163)
  ·
    refine ⟨7905686093246677489053245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5270457395497784992702163 7905686093246677489053245)
    ·
      refine ⟨2964632284967504058394967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7905686093246677489053245 2964632284967504058394967)
      ·
        refine ⟨4446948427451256087592451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2964632284967504058394967 4446948427451256087592451)
        ·
          refine ⟨6670422641176884131388677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4446948427451256087592451 6670422641176884131388677)
          ·
            refine ⟨1250704245220665774635377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6670422641176884131388677 1250704245220665774635377)
            ·
              refine ⟨938028183915499330976533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1250704245220665774635377 938028183915499330976533)
              ·
                refine ⟨43970071121039031139525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 938028183915499330976533 43970071121039031139525)
                ·
                  rfl

theorem cell19_144503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 6].length) (baseStart_144503 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_144503 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_144503 prefixEnd_144503 := by exact prefixLift 144503
  have htrace : WordTrace (prefixWord ++ tailWord_144503) baseStart_144503 baseEnd_144503 := by
    simpa [prefixWord, tailWord_144503, baseEnd_144503] using wordTrace_append hprefix tailTrace_144503
  have hstable : (prefixWord ++ tailWord_144503).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144503).length < 2 ^ (prefixWord ++ tailWord_144503).sum := by decide
  have hdescent : baseEnd_144503 < baseStart_144503 := by decide
  rcases family_descends (prefixWord ++ tailWord_144503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144510 : List Nat := [4, 2, 4, 1, 2, 1, 2, 3]
def baseStart_144510 : Nat := 118140960795 + 144510 * 2 ^ 59
def prefixEnd_144510 : Nat := 4983230072969 + 3 ^ 40 * 144510 * 2
def baseEnd_144510 : Nat := 43972201114865088983951

theorem tailTrace_144510 : CollatzResearch.WordTrace tailWord_144510 prefixEnd_144510 43972201114865088983951 := by
  unfold tailWord_144510
  simp only [CollatzResearch.WordTrace]
  refine ⟨658839088309053148525873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3513808470981616792137989 658839088309053148525873)
  ·
    refine ⟨494129316231789861394405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 658839088309053148525873 494129316231789861394405)
    ·
      refine ⟨92649246793460599011451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 494129316231789861394405 92649246793460599011451)
      ·
        refine ⟨138973870190190898517177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92649246793460599011451 138973870190190898517177)
        ·
          refine ⟨104230402642643173887883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138973870190190898517177 104230402642643173887883)
          ·
            refine ⟨156345603963964760831825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104230402642643173887883 156345603963964760831825)
            ·
              refine ⟨117259202972973570623869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156345603963964760831825 117259202972973570623869)
              ·
                refine ⟨43972201114865088983951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117259202972973570623869 43972201114865088983951)
                ·
                  rfl

theorem cell19_144510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_144510 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_144510 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_144510 prefixEnd_144510 := by exact prefixLift 144510
  have htrace : WordTrace (prefixWord ++ tailWord_144510) baseStart_144510 baseEnd_144510 := by
    simpa [prefixWord, tailWord_144510, baseEnd_144510] using wordTrace_append hprefix tailTrace_144510
  have hstable : (prefixWord ++ tailWord_144510).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144510).length < 2 ^ (prefixWord ++ tailWord_144510).sum := by decide
  have hdescent : baseEnd_144510 < baseStart_144510 := by decide
  rcases family_descends (prefixWord ++ tailWord_144510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144596 : List Nat := [2, 4, 1, 4, 8]
def baseStart_144596 : Nat := 118140960795 + 144596 * 2 ^ 59
def prefixEnd_144596 : Nat := 4983230072969 + 3 ^ 40 * 144596 * 2
def baseEnd_144596 : Nat := 1629569244831198928615

theorem tailTrace_144596 : CollatzResearch.WordTrace tailWord_144596 prefixEnd_144596 1629569244831198928615 := by
  unfold tailWord_144596
  simp only [CollatzResearch.WordTrace]
  refine ⟨2636924692080430937918821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3515899589440574583891761 2636924692080430937918821)
  ·
    refine ⟨494423379765080800859779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2636924692080430937918821 494423379765080800859779)
    ·
      refine ⟨741635069647621201289669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 494423379765080800859779 741635069647621201289669)
      ·
        refine ⟨139056575558928975241813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 741635069647621201289669 139056575558928975241813)
        ·
          refine ⟨1629569244831198928615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 139056575558928975241813 1629569244831198928615)
          ·
            rfl

theorem cell19_144596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 8].length) (baseStart_144596 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_144596 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_144596 prefixEnd_144596 := by exact prefixLift 144596
  have htrace : WordTrace (prefixWord ++ tailWord_144596) baseStart_144596 baseEnd_144596 := by
    simpa [prefixWord, tailWord_144596, baseEnd_144596] using wordTrace_append hprefix tailTrace_144596
  have hstable : (prefixWord ++ tailWord_144596).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144596).length < 2 ^ (prefixWord ++ tailWord_144596).sum := by decide
  have hdescent : baseEnd_144596 < baseStart_144596 := by decide
  rcases family_descends (prefixWord ++ tailWord_144596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144613 : List Nat := [1, 3, 1, 4, 3, 2, 1, 4]
def baseStart_144613 : Nat := 118140960795 + 144613 * 2 ^ 59
def prefixEnd_144613 : Nat := 4983230072969 + 3 ^ 40 * 144613 * 2
def baseEnd_144613 : Nat := 44003542452591368694781

theorem tailTrace_144613 : CollatzResearch.WordTrace tailWord_144613 prefixEnd_144613 44003542452591368694781 := by
  unfold tailWord_144613
  simp only [CollatzResearch.WordTrace]
  refine ⟨5274469425099273779206493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3516312950066182519470995 5274469425099273779206493)
  ·
    refine ⟨1977926034412227667202435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5274469425099273779206493 1977926034412227667202435)
    ·
      refine ⟨2966889051618341500803653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1977926034412227667202435 2966889051618341500803653)
      ·
        refine ⟨556291697178439031400685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2966889051618341500803653 556291697178439031400685)
        ·
          refine ⟨208609386441914636775257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 556291697178439031400685 208609386441914636775257)
          ·
            refine ⟨156457039831435977581443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 208609386441914636775257 156457039831435977581443)
            ·
              refine ⟨234685559747153966372165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156457039831435977581443 234685559747153966372165)
              ·
                refine ⟨44003542452591368694781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 234685559747153966372165 44003542452591368694781)
                ·
                  rfl

theorem cell19_144613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 4].length) (baseStart_144613 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_144613 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_144613 prefixEnd_144613 := by exact prefixLift 144613
  have htrace : WordTrace (prefixWord ++ tailWord_144613) baseStart_144613 baseEnd_144613 := by
    simpa [prefixWord, tailWord_144613, baseEnd_144613] using wordTrace_append hprefix tailTrace_144613
  have hstable : (prefixWord ++ tailWord_144613).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144613).length < 2 ^ (prefixWord ++ tailWord_144613).sum := by decide
  have hdescent : baseEnd_144613 < baseStart_144613 := by decide
  rcases family_descends (prefixWord ++ tailWord_144613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144634 : List Nat := [3, 1, 1, 1, 1, 4, 5, 3]
def baseStart_144634 : Nat := 118140960795 + 144634 * 2 ^ 59
def prefixEnd_144634 : Nat := 4983230072969 + 3 ^ 40 * 144634 * 2
def baseEnd_144634 : Nat := 44009932434069542228057

theorem tailTrace_144634 : CollatzResearch.WordTrace tailWord_144634 prefixEnd_144634 44009932434069542228057 := by
  unfold tailWord_144634
  simp only [CollatzResearch.WordTrace]
  refine ⟨1318808839505798591430239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3516823572015462910480637 1318808839505798591430239)
  ·
    refine ⟨1978213259258697887145359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1318808839505798591430239 1978213259258697887145359)
    ·
      refine ⟨2967319888888046830718039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1978213259258697887145359 2967319888888046830718039)
      ·
        refine ⟨4450979833332070246077059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2967319888888046830718039 4450979833332070246077059)
        ·
          refine ⟨6676469749998105369115589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4450979833332070246077059 6676469749998105369115589)
          ·
            refine ⟨1251838078124644756709173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6676469749998105369115589 1251838078124644756709173)
            ·
              refine ⟨117359819824185445941485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1251838078124644756709173 117359819824185445941485)
              ·
                refine ⟨44009932434069542228057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117359819824185445941485 44009932434069542228057)
                ·
                  rfl

theorem cell19_144634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_144634 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_144634 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_144634 prefixEnd_144634 := by exact prefixLift 144634
  have htrace : WordTrace (prefixWord ++ tailWord_144634) baseStart_144634 baseEnd_144634 := by
    simpa [prefixWord, tailWord_144634, baseEnd_144634] using wordTrace_append hprefix tailTrace_144634
  have hstable : (prefixWord ++ tailWord_144634).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144634).length < 2 ^ (prefixWord ++ tailWord_144634).sum := by decide
  have hdescent : baseEnd_144634 < baseStart_144634 := by decide
  rcases family_descends (prefixWord ++ tailWord_144634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144689 : List Nat := [1, 2, 2, 3, 3, 3, 2, 3]
def baseStart_144689 : Nat := 118140960795 + 144689 * 2 ^ 59
def prefixEnd_144689 : Nat := 4983230072969 + 3 ^ 40 * 144689 * 2
def baseEnd_144689 : Nat := 44026668099845711005685

theorem tailTrace_144689 : CollatzResearch.WordTrace tailWord_144689 prefixEnd_144689 44026668099845711005685 := by
  unfold tailWord_144689
  simp only [CollatzResearch.WordTrace]
  refine ⟨5277241372823938758973121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3518160915215959172648747 5277241372823938758973121)
  ·
    refine ⟨3957931029617954069229841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5277241372823938758973121 3957931029617954069229841)
    ·
      refine ⟨2968448272213465551922381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3957931029617954069229841 2968448272213465551922381)
      ·
        refine ⟨1113168102080049581970893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2968448272213465551922381 1113168102080049581970893)
        ·
          refine ⟨417438038280018593239085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1113168102080049581970893 417438038280018593239085)
          ·
            refine ⟨156539264355006972464657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 417438038280018593239085 156539264355006972464657)
            ·
              refine ⟨117404448266255229348493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156539264355006972464657 117404448266255229348493)
              ·
                refine ⟨44026668099845711005685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117404448266255229348493 44026668099845711005685)
                ·
                  rfl

theorem cell19_144689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 3].length) (baseStart_144689 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_144689 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_144689 prefixEnd_144689 := by exact prefixLift 144689
  have htrace : WordTrace (prefixWord ++ tailWord_144689) baseStart_144689 baseEnd_144689 := by
    simpa [prefixWord, tailWord_144689, baseEnd_144689] using wordTrace_append hprefix tailTrace_144689
  have hstable : (prefixWord ++ tailWord_144689).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144689).length < 2 ^ (prefixWord ++ tailWord_144689).sum := by decide
  have hdescent : baseEnd_144689 < baseStart_144689 := by decide
  rcases family_descends (prefixWord ++ tailWord_144689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144691 : List Nat := [1, 1, 1, 2, 5, 2, 4, 3]
def baseStart_144691 : Nat := 118140960795 + 144691 * 2 ^ 59
def prefixEnd_144691 : Nat := 4983230072969 + 3 ^ 40 * 144691 * 2
def baseEnd_144691 : Nat := 44027276669510298961235

theorem tailTrace_144691 : CollatzResearch.WordTrace tailWord_144691 prefixEnd_144691 44027276669510298961235 := by
  unfold tailWord_144691
  simp only [CollatzResearch.WordTrace]
  refine ⟨5277314318816693100545927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3518209545877795400363951 5277314318816693100545927)
  ·
    refine ⟨7915971478225039650818891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5277314318816693100545927 7915971478225039650818891)
    ·
      refine ⟨11873957217337559476228337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7915971478225039650818891 11873957217337559476228337)
      ·
        refine ⟨8905467913003169607171253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11873957217337559476228337 8905467913003169607171253)
        ·
          refine ⟨834887616844047150672305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8905467913003169607171253 834887616844047150672305)
          ·
            refine ⟨626165712633035363004229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 834887616844047150672305 626165712633035363004229)
            ·
              refine ⟨117406071118694130563293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 626165712633035363004229 117406071118694130563293)
              ·
                refine ⟨44027276669510298961235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117406071118694130563293 44027276669510298961235)
                ·
                  rfl

theorem cell19_144691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 3].length) (baseStart_144691 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_144691 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_144691 prefixEnd_144691 := by exact prefixLift 144691
  have htrace : WordTrace (prefixWord ++ tailWord_144691) baseStart_144691 baseEnd_144691 := by
    simpa [prefixWord, tailWord_144691, baseEnd_144691] using wordTrace_append hprefix tailTrace_144691
  have hstable : (prefixWord ++ tailWord_144691).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144691).length < 2 ^ (prefixWord ++ tailWord_144691).sum := by decide
  have hdescent : baseEnd_144691 < baseStart_144691 := by decide
  rcases family_descends (prefixWord ++ tailWord_144691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144708 : List Nat := [2, 3, 4, 1, 1, 3, 5]
def baseStart_144708 : Nat := 118140960795 + 144708 * 2 ^ 59
def prefixEnd_144708 : Nat := 4983230072969 + 3 ^ 40 * 144708 * 2
def baseEnd_144708 : Nat := 14677483170553098861137

theorem tailTrace_144708 : CollatzResearch.WordTrace tailWord_144708 prefixEnd_144708 14677483170553098861137 := by
  unfold tailWord_144708
  simp only [CollatzResearch.WordTrace]
  refine ⟨2638967179877552501957389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3518622906503403335943185 2638967179877552501957389)
  ·
    refine ⟨989612692454082188234021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2638967179877552501957389 989612692454082188234021)
    ·
      refine ⟨185552379835140410293879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 989612692454082188234021 185552379835140410293879)
      ·
        refine ⟨278328569752710615440819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185552379835140410293879 278328569752710615440819)
        ·
          refine ⟨417492854629065923161229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278328569752710615440819 417492854629065923161229)
          ·
            refine ⟨156559820485899721185461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 417492854629065923161229 156559820485899721185461)
            ·
              refine ⟨14677483170553098861137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 156559820485899721185461 14677483170553098861137)
              ·
                rfl

theorem cell19_144708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 5].length) (baseStart_144708 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_144708 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_144708 prefixEnd_144708 := by exact prefixLift 144708
  have htrace : WordTrace (prefixWord ++ tailWord_144708) baseStart_144708 baseEnd_144708 := by
    simpa [prefixWord, tailWord_144708, baseEnd_144708] using wordTrace_append hprefix tailTrace_144708
  have hstable : (prefixWord ++ tailWord_144708).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144708).length < 2 ^ (prefixWord ++ tailWord_144708).sum := by decide
  have hdescent : baseEnd_144708 < baseStart_144708 := by decide
  rcases family_descends (prefixWord ++ tailWord_144708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144769 : List Nat := [1, 2, 4, 3, 9]
def baseStart_144769 : Nat := 118140960795 + 144769 * 2 ^ 59
def prefixEnd_144769 : Nat := 4983230072969 + 3 ^ 40 * 144769 * 2
def baseEnd_144769 : Nat := 1631518921719601082507

theorem tailTrace_144769 : CollatzResearch.WordTrace tailWord_144769 prefixEnd_144769 1631518921719601082507 := by
  unfold tailWord_144769
  simp only [CollatzResearch.WordTrace]
  refine ⟨5280159212534112421885361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3520106141689408281256907 5280159212534112421885361)
  ·
    refine ⟨3960119409400584316414021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5280159212534112421885361 3960119409400584316414021)
    ·
      refine ⟨742522389262609559327629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3960119409400584316414021 742522389262609559327629)
      ·
        refine ⟨278445895973478584747861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 742522389262609559327629 278445895973478584747861)
        ·
          refine ⟨1631518921719601082507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 278445895973478584747861 1631518921719601082507)
          ·
            rfl

theorem cell19_144769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 9].length) (baseStart_144769 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_144769 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_144769 prefixEnd_144769 := by exact prefixLift 144769
  have htrace : WordTrace (prefixWord ++ tailWord_144769) baseStart_144769 baseEnd_144769 := by
    simpa [prefixWord, tailWord_144769, baseEnd_144769] using wordTrace_append hprefix tailTrace_144769
  have hstable : (prefixWord ++ tailWord_144769).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144769).length < 2 ^ (prefixWord ++ tailWord_144769).sum := by decide
  have hdescent : baseEnd_144769 < baseStart_144769 := by decide
  rcases family_descends (prefixWord ++ tailWord_144769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144782 : List Nat := [4, 1, 1, 4, 3, 1, 1, 4]
def baseStart_144782 : Nat := 118140960795 + 144782 * 2 ^ 59
def prefixEnd_144782 : Nat := 4983230072969 + 3 ^ 40 * 144782 * 2
def baseEnd_144782 : Nat := 44054966589249050938765

theorem tailTrace_144782 : CollatzResearch.WordTrace tailWord_144782 prefixEnd_144782 44054966589249050938765 := by
  unfold tailWord_144782
  simp only [CollatzResearch.WordTrace]
  refine ⟨660079170185876955263575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3520422240991343761405733 660079170185876955263575)
  ·
    refine ⟨990118755278815432895363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 660079170185876955263575 990118755278815432895363)
    ·
      refine ⟨1485178132918223149343045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 990118755278815432895363 1485178132918223149343045)
      ·
        refine ⟨278470899922166840501821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1485178132918223149343045 278470899922166840501821)
        ·
          refine ⟨104426587470812565188183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 278470899922166840501821 104426587470812565188183)
          ·
            refine ⟨156639881206218847782275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104426587470812565188183 156639881206218847782275)
            ·
              refine ⟨234959821809328271673413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156639881206218847782275 234959821809328271673413)
              ·
                refine ⟨44054966589249050938765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 234959821809328271673413 44054966589249050938765)
                ·
                  rfl

theorem cell19_144782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_144782 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_144782 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_144782 prefixEnd_144782 := by exact prefixLift 144782
  have htrace : WordTrace (prefixWord ++ tailWord_144782) baseStart_144782 baseEnd_144782 := by
    simpa [prefixWord, tailWord_144782, baseEnd_144782] using wordTrace_append hprefix tailTrace_144782
  have hstable : (prefixWord ++ tailWord_144782).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144782).length < 2 ^ (prefixWord ++ tailWord_144782).sum := by decide
  have hdescent : baseEnd_144782 < baseStart_144782 := by decide
  rcases family_descends (prefixWord ++ tailWord_144782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144898 : List Nat := [3, 4, 1, 2, 1, 2, 2, 4]
def baseStart_144898 : Nat := 118140960795 + 144898 * 2 ^ 59
def prefixEnd_144898 : Nat := 4983230072969 + 3 ^ 40 * 144898 * 2
def baseEnd_144898 : Nat := 44090263629795152360671

theorem tailTrace_144898 : CollatzResearch.WordTrace tailWord_144898 prefixEnd_144898 44090263629795152360671 := by
  unfold tailWord_144898
  simp only [CollatzResearch.WordTrace]
  refine ⟨1321216057266691863332837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3523242819377844968887565 1321216057266691863332837)
  ·
    refine ⟨247728010737504724374907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1321216057266691863332837 247728010737504724374907)
    ·
      refine ⟨371592016106257086562361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247728010737504724374907 371592016106257086562361)
      ·
        refine ⟨278694012079692814921771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 371592016106257086562361 278694012079692814921771)
        ·
          refine ⟨418041018119539222382657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278694012079692814921771 418041018119539222382657)
          ·
            refine ⟨313530763589654416786993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 418041018119539222382657 313530763589654416786993)
            ·
              refine ⟨235148072692240812590245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 313530763589654416786993 235148072692240812590245)
              ·
                refine ⟨44090263629795152360671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 235148072692240812590245 44090263629795152360671)
                ·
                  rfl

theorem cell19_144898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_144898 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_144898 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_144898 prefixEnd_144898 := by exact prefixLift 144898
  have htrace : WordTrace (prefixWord ++ tailWord_144898) baseStart_144898 baseEnd_144898 := by
    simpa [prefixWord, tailWord_144898, baseEnd_144898] using wordTrace_append hprefix tailTrace_144898
  have hstable : (prefixWord ++ tailWord_144898).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144898).length < 2 ^ (prefixWord ++ tailWord_144898).sum := by decide
  have hdescent : baseEnd_144898 < baseStart_144898 := by decide
  rcases family_descends (prefixWord ++ tailWord_144898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144959 : List Nat := [1, 1, 2, 2, 3, 3, 3, 4]
def baseStart_144959 : Nat := 118140960795 + 144959 * 2 ^ 59
def prefixEnd_144959 : Nat := 4983230072969 + 3 ^ 40 * 144959 * 2
def baseEnd_144959 : Nat := 44108825004565085004949

theorem tailTrace_144959 : CollatzResearch.WordTrace tailWord_144959 prefixEnd_144959 44108825004565085004949 := by
  unfold tailWord_144959
  simp only [CollatzResearch.WordTrace]
  refine ⟨5287089081845774871301931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3524726054563849914201287 5287089081845774871301931)
  ·
    refine ⟨7930633622768662306952897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5287089081845774871301931 7930633622768662306952897)
    ·
      refine ⟨5947975217076496730214673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7930633622768662306952897 5947975217076496730214673)
      ·
        refine ⟨4460981412807372547661005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5947975217076496730214673 4460981412807372547661005)
        ·
          refine ⟨1672868029802764705372877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4460981412807372547661005 1672868029802764705372877)
          ·
            refine ⟨627325511176036764514829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1672868029802764705372877 627325511176036764514829)
            ·
              refine ⟨235247066691013786693061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 627325511176036764514829 235247066691013786693061)
              ·
                refine ⟨44108825004565085004949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 235247066691013786693061 44108825004565085004949)
                ·
                  rfl

theorem cell19_144959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 4].length) (baseStart_144959 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_144959 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_144959 prefixEnd_144959 := by exact prefixLift 144959
  have htrace : WordTrace (prefixWord ++ tailWord_144959) baseStart_144959 baseEnd_144959 := by
    simpa [prefixWord, tailWord_144959, baseEnd_144959] using wordTrace_append hprefix tailTrace_144959
  have hstable : (prefixWord ++ tailWord_144959).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144959).length < 2 ^ (prefixWord ++ tailWord_144959).sum := by decide
  have hdescent : baseEnd_144959 < baseStart_144959 := by decide
  rcases family_descends (prefixWord ++ tailWord_144959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144997 : List Nat := [1, 3, 1, 3, 3, 2, 6]
def baseStart_144997 : Nat := 118140960795 + 144997 * 2 ^ 59
def prefixEnd_144997 : Nat := 4983230072969 + 3 ^ 40 * 144997 * 2
def baseEnd_144997 : Nat := 14706795942730752053467

theorem tailTrace_144997 : CollatzResearch.WordTrace tailWord_144997 prefixEnd_144997 14706795942730752053467 := by
  unfold tailWord_144997
  simp only [CollatzResearch.WordTrace]
  refine ⟨5288475055708107361185245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3525650037138738240790163 5288475055708107361185245)
  ·
    refine ⟨1983178145890540260444467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5288475055708107361185245 1983178145890540260444467)
    ·
      refine ⟨2974767218835810390666701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1983178145890540260444467 2974767218835810390666701)
      ·
        refine ⟨1115537707063428896500013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2974767218835810390666701 1115537707063428896500013)
        ·
          refine ⟨418326640148785836187505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1115537707063428896500013 418326640148785836187505)
          ·
            refine ⟨313744980111589377140629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 418326640148785836187505 313744980111589377140629)
            ·
              refine ⟨14706795942730752053467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 313744980111589377140629 14706795942730752053467)
              ·
                rfl

theorem cell19_144997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 6].length) (baseStart_144997 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_144997 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_144997 prefixEnd_144997 := by exact prefixLift 144997
  have htrace : WordTrace (prefixWord ++ tailWord_144997) baseStart_144997 baseEnd_144997 := by
    simpa [prefixWord, tailWord_144997, baseEnd_144997] using wordTrace_append hprefix tailTrace_144997
  have hstable : (prefixWord ++ tailWord_144997).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144997).length < 2 ^ (prefixWord ++ tailWord_144997).sum := by decide
  have hdescent : baseEnd_144997 < baseStart_144997 := by decide
  rcases family_descends (prefixWord ++ tailWord_144997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145052 : List Nat := [2, 2, 3, 2, 3, 2, 5]
def baseStart_145052 : Nat := 118140960795 + 145052 * 2 ^ 59
def prefixEnd_145052 : Nat := 4983230072969 + 3 ^ 40 * 145052 * 2
def baseEnd_145052 : Nat := 14712374497989474979343

theorem tailTrace_145052 : CollatzResearch.WordTrace tailWord_145052 prefixEnd_145052 14712374497989474979343 := by
  unfold tailWord_145052
  simp only [CollatzResearch.WordTrace]
  refine ⟨2645240535254425877218705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3526987380339234502958273 2645240535254425877218705)
  ·
    refine ⟨1983930401440819407914029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2645240535254425877218705 1983930401440819407914029)
    ·
      refine ⟨743973900540307277967761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1983930401440819407914029 743973900540307277967761)
      ·
        refine ⟨557980425405230458475821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 743973900540307277967761 557980425405230458475821)
        ·
          refine ⟨209242659526961421928433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 557980425405230458475821 209242659526961421928433)
          ·
            refine ⟨156931994645221066446325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209242659526961421928433 156931994645221066446325)
            ·
              refine ⟨14712374497989474979343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 156931994645221066446325 14712374497989474979343)
              ·
                rfl

theorem cell19_145052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 5].length) (baseStart_145052 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_145052 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_145052 prefixEnd_145052 := by exact prefixLift 145052
  have htrace : WordTrace (prefixWord ++ tailWord_145052) baseStart_145052 baseEnd_145052 := by
    simpa [prefixWord, tailWord_145052, baseEnd_145052] using wordTrace_append hprefix tailTrace_145052
  have hstable : (prefixWord ++ tailWord_145052).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145052).length < 2 ^ (prefixWord ++ tailWord_145052).sum := by decide
  have hdescent : baseEnd_145052 < baseStart_145052 := by decide
  rcases family_descends (prefixWord ++ tailWord_145052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145092 : List Nat := [2, 3, 3, 1, 1, 1, 1, 7]
def baseStart_145092 : Nat := 118140960795 + 145092 * 2 ^ 59
def prefixEnd_145092 : Nat := 4983230072969 + 3 ^ 40 * 145092 * 2
def baseEnd_145092 : Nat := 44149294887260184049031

theorem tailTrace_145092 : CollatzResearch.WordTrace tailWord_145092 prefixEnd_145092 44149294887260184049031 := by
  unfold tailWord_145092
  simp only [CollatzResearch.WordTrace]
  refine ⟨2645969995181969292946765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3527959993575959057262353 2645969995181969292946765)
  ·
    refine ⟨992238748193238484855037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2645969995181969292946765 992238748193238484855037)
    ·
      refine ⟨372089530572464431820639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 992238748193238484855037 372089530572464431820639)
      ·
        refine ⟨558134295858696647730959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372089530572464431820639 558134295858696647730959)
        ·
          refine ⟨837201443788044971596439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 558134295858696647730959 837201443788044971596439)
          ·
            refine ⟨1255802165682067457394659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 837201443788044971596439 1255802165682067457394659)
            ·
              refine ⟨1883703248523101186091989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1255802165682067457394659 1883703248523101186091989)
              ·
                refine ⟨44149294887260184049031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1883703248523101186091989 44149294887260184049031)
                ·
                  rfl

theorem cell19_145092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_145092 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_145092 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_145092 prefixEnd_145092 := by exact prefixLift 145092
  have htrace : WordTrace (prefixWord ++ tailWord_145092) baseStart_145092 baseEnd_145092 := by
    simpa [prefixWord, tailWord_145092, baseEnd_145092] using wordTrace_append hprefix tailTrace_145092
  have hstable : (prefixWord ++ tailWord_145092).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145092).length < 2 ^ (prefixWord ++ tailWord_145092).sum := by decide
  have hdescent : baseEnd_145092 < baseStart_145092 := by decide
  rcases family_descends (prefixWord ++ tailWord_145092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145113 : List Nat := [1, 2, 1, 2, 3, 10]
def baseStart_145113 : Nat := 118140960795 + 145113 * 2 ^ 59
def prefixEnd_145113 : Nat := 4983230072969 + 3 ^ 40 * 145113 * 2
def baseEnd_145113 : Nat := 4906187207637595286923

theorem tailTrace_145113 : CollatzResearch.WordTrace tailWord_145113 prefixEnd_145113 4906187207637595286923 := by
  unfold tailWord_145113
  simp only [CollatzResearch.WordTrace]
  refine ⟨5292705923287859172407993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3528470615525239448271995 5292705923287859172407993)
  ·
    refine ⟨3969529442465894379305995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5292705923287859172407993 3969529442465894379305995)
    ·
      refine ⟨5954294163698841568958993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3969529442465894379305995 5954294163698841568958993)
      ·
        refine ⟨4465720622774131176719245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5954294163698841568958993 4465720622774131176719245)
        ·
          refine ⟨1674645233540299191269717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4465720622774131176719245 1674645233540299191269717)
          ·
            refine ⟨4906187207637595286923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1674645233540299191269717 4906187207637595286923)
            ·
              rfl

theorem cell19_145113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 10].length) (baseStart_145113 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_145113 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_145113 prefixEnd_145113 := by exact prefixLift 145113
  have htrace : WordTrace (prefixWord ++ tailWord_145113) baseStart_145113 baseEnd_145113 := by
    simpa [prefixWord, tailWord_145113, baseEnd_145113] using wordTrace_append hprefix tailTrace_145113
  have hstable : (prefixWord ++ tailWord_145113).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145113).length < 2 ^ (prefixWord ++ tailWord_145113).sum := by decide
  have hdescent : baseEnd_145113 < baseStart_145113 := by decide
  rcases family_descends (prefixWord ++ tailWord_145113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145128 : List Nat := [2, 1, 4, 1, 3, 3, 1, 4]
def baseStart_145128 : Nat := 118140960795 + 145128 * 2 ^ 59
def prefixEnd_145128 : Nat := 4983230072969 + 3 ^ 40 * 145128 * 2
def baseEnd_145128 : Nat := 44160249141222767248933

theorem tailTrace_145128 : CollatzResearch.WordTrace tailWord_145128 prefixEnd_145128 44160249141222767248933 := by
  unfold tailWord_145128
  simp only [CollatzResearch.WordTrace]
  refine ⟨2646626509116758367102019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3528835345489011156136025 2646626509116758367102019)
  ·
    refine ⟨3969939763675137550653029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2646626509116758367102019 3969939763675137550653029)
    ·
      refine ⟨744363705689088290747443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3969939763675137550653029 744363705689088290747443)
      ·
        refine ⟨1116545558533632436121165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 744363705689088290747443 1116545558533632436121165)
        ·
          refine ⟨418704584450112163545437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1116545558533632436121165 418704584450112163545437)
          ·
            refine ⟨157014219168792061329539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 418704584450112163545437 157014219168792061329539)
            ·
              refine ⟨235521328753188091994309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157014219168792061329539 235521328753188091994309)
              ·
                refine ⟨44160249141222767248933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 235521328753188091994309 44160249141222767248933)
                ·
                  rfl

theorem cell19_145128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 4].length) (baseStart_145128 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_145128 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_145128 prefixEnd_145128 := by exact prefixLift 145128
  have htrace : WordTrace (prefixWord ++ tailWord_145128) baseStart_145128 baseEnd_145128 := by
    simpa [prefixWord, tailWord_145128, baseEnd_145128] using wordTrace_append hprefix tailTrace_145128
  have hstable : (prefixWord ++ tailWord_145128).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145128).length < 2 ^ (prefixWord ++ tailWord_145128).sum := by decide
  have hdescent : baseEnd_145128 < baseStart_145128 := by decide
  rcases family_descends (prefixWord ++ tailWord_145128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145130 : List Nat := [3, 1, 3, 1, 1, 1, 5, 4]
def baseStart_145130 : Nat := 118140960795 + 145130 * 2 ^ 59
def prefixEnd_145130 : Nat := 4983230072969 + 3 ^ 40 * 145130 * 2
def baseEnd_145130 : Nat := 44160857710887355204483

theorem tailTrace_145130 : CollatzResearch.WordTrace tailWord_145130 prefixEnd_145130 44160857710887355204483 := by
  unfold tailWord_145130
  simp only [CollatzResearch.WordTrace]
  refine ⟨1323331491056567768944211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3528883976150847383851229 1323331491056567768944211)
  ·
    refine ⟨1984997236584851653416317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1323331491056567768944211 1984997236584851653416317)
    ·
      refine ⟨744373963719319370031119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1984997236584851653416317 744373963719319370031119)
      ·
        refine ⟨1116560945578979055046679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 744373963719319370031119 1116560945578979055046679)
        ·
          refine ⟨1674841418368468582570019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1116560945578979055046679 1674841418368468582570019)
          ·
            refine ⟨2512262127552702873855029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1674841418368468582570019 2512262127552702873855029)
            ·
              refine ⟨235524574458065894423909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2512262127552702873855029 235524574458065894423909)
              ·
                refine ⟨44160857710887355204483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 235524574458065894423909 44160857710887355204483)
                ·
                  rfl

theorem cell19_145130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_145130 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_145130 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_145130 prefixEnd_145130 := by exact prefixLift 145130
  have htrace : WordTrace (prefixWord ++ tailWord_145130) baseStart_145130 baseEnd_145130 := by
    simpa [prefixWord, tailWord_145130, baseEnd_145130] using wordTrace_append hprefix tailTrace_145130
  have hstable : (prefixWord ++ tailWord_145130).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145130).length < 2 ^ (prefixWord ++ tailWord_145130).sum := by decide
  have hdescent : baseEnd_145130 < baseStart_145130 := by decide
  rcases family_descends (prefixWord ++ tailWord_145130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145151 : List Nat := [1, 1, 2, 2, 1, 3, 2, 7]
def baseStart_145151 : Nat := 118140960795 + 145151 * 2 ^ 59
def prefixEnd_145151 : Nat := 4983230072969 + 3 ^ 40 * 145151 * 2
def baseEnd_145151 : Nat := 44167247692365528737759

theorem tailTrace_145151 : CollatzResearch.WordTrace tailWord_145151 prefixEnd_145151 44167247692365528737759 := by
  unfold tailWord_145151
  simp only [CollatzResearch.WordTrace]
  refine ⟨5294091897150191662291307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3529394598100127774860871 5294091897150191662291307)
  ·
    refine ⟨7941137845725287493436961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5294091897150191662291307 7941137845725287493436961)
    ·
      refine ⟨5955853384293965620077721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7941137845725287493436961 5955853384293965620077721)
      ·
        refine ⟨4466890038220474215058291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5955853384293965620077721 4466890038220474215058291)
        ·
          refine ⟨6700335057330711322587437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4466890038220474215058291 6700335057330711322587437)
          ·
            refine ⟨2512625646499016745970289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6700335057330711322587437 2512625646499016745970289)
            ·
              refine ⟨1884469234874262559477717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2512625646499016745970289 1884469234874262559477717)
              ·
                refine ⟨44167247692365528737759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1884469234874262559477717 44167247692365528737759)
                ·
                  rfl

theorem cell19_145151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 7].length) (baseStart_145151 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_145151 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_145151 prefixEnd_145151 := by exact prefixLift 145151
  have htrace : WordTrace (prefixWord ++ tailWord_145151) baseStart_145151 baseEnd_145151 := by
    simpa [prefixWord, tailWord_145151, baseEnd_145151] using wordTrace_append hprefix tailTrace_145151
  have hstable : (prefixWord ++ tailWord_145151).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145151).length < 2 ^ (prefixWord ++ tailWord_145151).sum := by decide
  have hdescent : baseEnd_145151 < baseStart_145151 := by decide
  rcases family_descends (prefixWord ++ tailWord_145151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145204 : List Nat := [2, 5, 1, 1, 2, 2, 1, 5]
def baseStart_145204 : Nat := 118140960795 + 145204 * 2 ^ 59
def prefixEnd_145204 : Nat := 4983230072969 + 3 ^ 40 * 145204 * 2
def baseEnd_145204 : Nat := 44183374788477109559837

theorem tailTrace_145204 : CollatzResearch.WordTrace tailWord_145204 prefixEnd_145204 44183374788477109559837 := by
  unfold tailWord_145204
  simp only [CollatzResearch.WordTrace]
  refine ⟨2648012482979090856985333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3530683310638787809313777 2648012482979090856985333)
  ·
    refine ⟨248251170279289767842375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2648012482979090856985333 248251170279289767842375)
    ·
      refine ⟨372376755418934651763563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248251170279289767842375 372376755418934651763563)
      ·
        refine ⟨558565133128401977645345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372376755418934651763563 558565133128401977645345)
        ·
          refine ⟨418923849846301483234009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 558565133128401977645345 418923849846301483234009)
          ·
            refine ⟨314192887384726112425507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 418923849846301483234009 314192887384726112425507)
            ·
              refine ⟨471289331077089168638261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 314192887384726112425507 471289331077089168638261)
              ·
                refine ⟨44183374788477109559837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 471289331077089168638261 44183374788477109559837)
                ·
                  rfl

theorem cell19_145204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_145204 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_145204 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_145204 prefixEnd_145204 := by exact prefixLift 145204
  have htrace : WordTrace (prefixWord ++ tailWord_145204) baseStart_145204 baseEnd_145204 := by
    simpa [prefixWord, tailWord_145204, baseEnd_145204] using wordTrace_append hprefix tailTrace_145204
  have hstable : (prefixWord ++ tailWord_145204).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145204).length < 2 ^ (prefixWord ++ tailWord_145204).sum := by decide
  have hdescent : baseEnd_145204 < baseStart_145204 := by decide
  rcases family_descends (prefixWord ++ tailWord_145204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145265 : List Nat := [1, 2, 2, 2, 1, 3, 1, 7]
def baseStart_145265 : Nat := 118140960795 + 145265 * 2 ^ 59
def prefixEnd_145265 : Nat := 4983230072969 + 3 ^ 40 * 145265 * 2
def baseEnd_145265 : Nat := 44201936163247042204115

theorem tailTrace_145265 : CollatzResearch.WordTrace tailWord_145265 prefixEnd_145265 44201936163247042204115 := by
  unfold tailWord_145265
  simp only [CollatzResearch.WordTrace]
  refine ⟨5298249818737189131941249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3532166545824792754627499 5298249818737189131941249)
  ·
    refine ⟨3973687364052891848955937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5298249818737189131941249 3973687364052891848955937)
    ·
      refine ⟨2980265523039668886716953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3973687364052891848955937 2980265523039668886716953)
      ·
        refine ⟨2235199142279751665037715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2980265523039668886716953 2235199142279751665037715)
        ·
          refine ⟨3352798713419627497556573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2235199142279751665037715 3352798713419627497556573)
          ·
            refine ⟨1257299517532360311583715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3352798713419627497556573 1257299517532360311583715)
            ·
              refine ⟨1885949276298540467375573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1257299517532360311583715 1885949276298540467375573)
              ·
                refine ⟨44201936163247042204115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1885949276298540467375573 44201936163247042204115)
                ·
                  rfl

theorem cell19_145265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 7].length) (baseStart_145265 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_145265 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_145265 prefixEnd_145265 := by exact prefixLift 145265
  have htrace : WordTrace (prefixWord ++ tailWord_145265) baseStart_145265 baseEnd_145265 := by
    simpa [prefixWord, tailWord_145265, baseEnd_145265] using wordTrace_append hprefix tailTrace_145265
  have hstable : (prefixWord ++ tailWord_145265).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145265).length < 2 ^ (prefixWord ++ tailWord_145265).sum := by decide
  have hdescent : baseEnd_145265 < baseStart_145265 := by decide
  rcases family_descends (prefixWord ++ tailWord_145265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145282 : List Nat := [3, 4, 2, 10]
def baseStart_145282 : Nat := 118140960795 + 145282 * 2 ^ 59
def prefixEnd_145282 : Nat := 4983230072969 + 3 ^ 40 * 145282 * 2
def baseEnd_145282 : Nat := 545766777844395553411

theorem tailTrace_145282 : CollatzResearch.WordTrace tailWord_145282 prefixEnd_145282 545766777844395553411 := by
  unfold tailWord_145282
  simp only [CollatzResearch.WordTrace]
  refine ⟨1324717464918900258827525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3532579906450400690206733 1324717464918900258827525)
  ·
    refine ⟨248384524672293798530161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1324717464918900258827525 248384524672293798530161)
    ·
      refine ⟨186288393504220348897621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248384524672293798530161 186288393504220348897621)
      ·
        refine ⟨545766777844395553411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 186288393504220348897621 545766777844395553411)
        ·
          rfl

theorem cell19_145282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 10].length) (baseStart_145282 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_145282 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_145282 prefixEnd_145282 := by exact prefixLift 145282
  have htrace : WordTrace (prefixWord ++ tailWord_145282) baseStart_145282 baseEnd_145282 := by
    simpa [prefixWord, tailWord_145282, baseEnd_145282] using wordTrace_append hprefix tailTrace_145282
  have hstable : (prefixWord ++ tailWord_145282).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145282).length < 2 ^ (prefixWord ++ tailWord_145282).sum := by decide
  have hdescent : baseEnd_145282 < baseStart_145282 := by decide
  rcases family_descends (prefixWord ++ tailWord_145282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145373 : List Nat := [1, 4, 3, 1, 3, 2, 2, 3]
def baseStart_145373 : Nat := 118140960795 + 145373 * 2 ^ 59
def prefixEnd_145373 : Nat := 4983230072969 + 3 ^ 40 * 145373 * 2
def baseEnd_145373 : Nat := 44234798925134791803821

theorem tailTrace_145373 : CollatzResearch.WordTrace tailWord_145373 prefixEnd_145373 44234798925134791803821 := by
  unfold tailWord_145373
  simp only [CollatzResearch.WordTrace]
  refine ⟨5302188902345923576872773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3534792601563949051248515 5302188902345923576872773)
  ·
    refine ⟨994160419189860670663645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5302188902345923576872773 994160419189860670663645)
    ·
      refine ⟨372810157196197751498867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 994160419189860670663645 372810157196197751498867)
      ·
        refine ⟨559215235794296627248301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372810157196197751498867 559215235794296627248301)
        ·
          refine ⟨209705713422861235218113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 559215235794296627248301 209705713422861235218113)
          ·
            refine ⟨157279285067145926413585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209705713422861235218113 157279285067145926413585)
            ·
              refine ⟨117959463800359444810189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157279285067145926413585 117959463800359444810189)
              ·
                refine ⟨44234798925134791803821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117959463800359444810189 44234798925134791803821)
                ·
                  rfl

theorem cell19_145373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 3].length) (baseStart_145373 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_145373 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_145373 prefixEnd_145373 := by exact prefixLift 145373
  have htrace : WordTrace (prefixWord ++ tailWord_145373) baseStart_145373 baseEnd_145373 := by
    simpa [prefixWord, tailWord_145373, baseEnd_145373] using wordTrace_append hprefix tailTrace_145373
  have hstable : (prefixWord ++ tailWord_145373).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145373).length < 2 ^ (prefixWord ++ tailWord_145373).sum := by decide
  have hdescent : baseEnd_145373 < baseStart_145373 := by decide
  rcases family_descends (prefixWord ++ tailWord_145373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145375 : List Nat := [1, 1, 2, 3, 4, 3, 2, 3]
def baseStart_145375 : Nat := 118140960795 + 145375 * 2 ^ 59
def prefixEnd_145375 : Nat := 4983230072969 + 3 ^ 40 * 145375 * 2
def baseEnd_145375 : Nat := 44235407494799379759371

theorem tailTrace_145375 : CollatzResearch.WordTrace tailWord_145375 prefixEnd_145375 44235407494799379759371 := by
  unfold tailWord_145375
  simp only [CollatzResearch.WordTrace]
  refine ⟨5302261848338677918445579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3534841232225785278963719 5302261848338677918445579)
  ·
    refine ⟨7953392772508016877668369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5302261848338677918445579 7953392772508016877668369)
    ·
      refine ⟨5965044579381012658251277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7953392772508016877668369 5965044579381012658251277)
      ·
        refine ⟨2236891717267879746844229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5965044579381012658251277 2236891717267879746844229)
        ·
          refine ⟨419417196987727452533293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2236891717267879746844229 419417196987727452533293)
          ·
            refine ⟨157281448870397794699985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 419417196987727452533293 157281448870397794699985)
            ·
              refine ⟨117961086652798346024989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157281448870397794699985 117961086652798346024989)
              ·
                refine ⟨44235407494799379759371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117961086652798346024989 44235407494799379759371)
                ·
                  rfl

theorem cell19_145375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 3].length) (baseStart_145375 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_145375 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_145375 prefixEnd_145375 := by exact prefixLift 145375
  have htrace : WordTrace (prefixWord ++ tailWord_145375) baseStart_145375 baseEnd_145375 := by
    simpa [prefixWord, tailWord_145375, baseEnd_145375] using wordTrace_append hprefix tailTrace_145375
  have hstable : (prefixWord ++ tailWord_145375).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145375).length < 2 ^ (prefixWord ++ tailWord_145375).sum := by decide
  have hdescent : baseEnd_145375 < baseStart_145375 := by decide
  rcases family_descends (prefixWord ++ tailWord_145375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145377 : List Nat := [1, 2, 3, 1, 2, 1, 6, 3]
def baseStart_145377 : Nat := 118140960795 + 145377 * 2 ^ 59
def prefixEnd_145377 : Nat := 4983230072969 + 3 ^ 40 * 145377 * 2
def baseEnd_145377 : Nat := 44236016064463967714921

theorem tailTrace_145377 : CollatzResearch.WordTrace tailWord_145377 prefixEnd_145377 44236016064463967714921 := by
  unfold tailWord_145377
  simp only [CollatzResearch.WordTrace]
  refine ⟨5302334794331432260018385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3534889862887621506678923 5302334794331432260018385)
  ·
    refine ⟨3976751095748574195013789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5302334794331432260018385 3976751095748574195013789)
    ·
      refine ⟨1491281660905715323130171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3976751095748574195013789 1491281660905715323130171)
      ·
        refine ⟨2236922491358572984695257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1491281660905715323130171 2236922491358572984695257)
        ·
          refine ⟨1677691868518929738521443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2236922491358572984695257 1677691868518929738521443)
          ·
            refine ⟨2516537802778394607782165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1677691868518929738521443 2516537802778394607782165)
            ·
              refine ⟨117962709505237247239789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2516537802778394607782165 117962709505237247239789)
              ·
                refine ⟨44236016064463967714921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117962709505237247239789 44236016064463967714921)
                ·
                  rfl

theorem cell19_145377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 3].length) (baseStart_145377 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_145377 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_145377 prefixEnd_145377 := by exact prefixLift 145377
  have htrace : WordTrace (prefixWord ++ tailWord_145377) baseStart_145377 baseEnd_145377 := by
    simpa [prefixWord, tailWord_145377, baseEnd_145377] using wordTrace_append hprefix tailTrace_145377
  have hstable : (prefixWord ++ tailWord_145377).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145377).length < 2 ^ (prefixWord ++ tailWord_145377).sum := by decide
  have hdescent : baseEnd_145377 < baseStart_145377 := by decide
  rcases family_descends (prefixWord ++ tailWord_145377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145415 : List Nat := [1, 1, 4, 3, 1, 3, 2, 4]
def baseStart_145415 : Nat := 118140960795 + 145415 * 2 ^ 59
def prefixEnd_145415 : Nat := 4983230072969 + 3 ^ 40 * 145415 * 2
def baseEnd_145415 : Nat := 44247578888091138870373

theorem tailTrace_145415 : CollatzResearch.WordTrace tailWord_145415 prefixEnd_145415 44247578888091138870373 := by
  unfold tailWord_145415
  simp only [CollatzResearch.WordTrace]
  refine ⟨5303720768193764749901699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3535813845462509833267799 5303720768193764749901699)
  ·
    refine ⟨7955581152290647124852549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5303720768193764749901699 7955581152290647124852549)
    ·
      refine ⟨1491671466054496335909853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7955581152290647124852549 1491671466054496335909853)
      ·
        refine ⟨559376799770436125966195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1491671466054496335909853 559376799770436125966195)
        ·
          refine ⟨839065199655654188949293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 559376799770436125966195 839065199655654188949293)
          ·
            refine ⟨314649449870870320855985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 839065199655654188949293 314649449870870320855985)
            ·
              refine ⟨235987087403152740641989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 314649449870870320855985 235987087403152740641989)
              ·
                refine ⟨44247578888091138870373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 235987087403152740641989 44247578888091138870373)
                ·
                  rfl

theorem cell19_145415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 4].length) (baseStart_145415 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_145415 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_145415 prefixEnd_145415 := by exact prefixLift 145415
  have htrace : WordTrace (prefixWord ++ tailWord_145415) baseStart_145415 baseEnd_145415 := by
    simpa [prefixWord, tailWord_145415, baseEnd_145415] using wordTrace_append hprefix tailTrace_145415
  have hstable : (prefixWord ++ tailWord_145415).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145415).length < 2 ^ (prefixWord ++ tailWord_145415).sum := by decide
  have hdescent : baseEnd_145415 < baseStart_145415 := by decide
  rcases family_descends (prefixWord ++ tailWord_145415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145472 : List Nat := [2, 1, 1, 2, 2, 6, 1, 4]
def baseStart_145472 : Nat := 118140960795 + 145472 * 2 ^ 59
def prefixEnd_145472 : Nat := 4983230072969 + 3 ^ 40 * 145472 * 2
def baseEnd_145472 : Nat := 44264923123531895603551

theorem tailTrace_145472 : CollatzResearch.WordTrace tailWord_145472 prefixEnd_145472 44264923123531895603551 := by
  unfold tailWord_145472
  simp only [CollatzResearch.WordTrace]
  refine ⟨2652899864493631742363335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3537199819324842323151113 2652899864493631742363335)
  ·
    refine ⟨3979349796740447613545003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2652899864493631742363335 3979349796740447613545003)
    ·
      refine ⟨5969024695110671420317505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3979349796740447613545003 5969024695110671420317505)
      ·
        refine ⟨4476768521333003565238129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5969024695110671420317505 4476768521333003565238129)
        ·
          refine ⟨3357576390999752673928597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4476768521333003565238129 3357576390999752673928597)
          ·
            refine ⟨157386393328113406590403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3357576390999752673928597 157386393328113406590403)
            ·
              refine ⟨236079589992170109885605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157386393328113406590403 236079589992170109885605)
              ·
                refine ⟨44264923123531895603551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 236079589992170109885605 44264923123531895603551)
                ·
                  rfl

theorem cell19_145472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 4].length) (baseStart_145472 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_145472 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_145472 prefixEnd_145472 := by exact prefixLift 145472
  have htrace : WordTrace (prefixWord ++ tailWord_145472) baseStart_145472 baseEnd_145472 := by
    simpa [prefixWord, tailWord_145472, baseEnd_145472] using wordTrace_append hprefix tailTrace_145472
  have hstable : (prefixWord ++ tailWord_145472).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145472).length < 2 ^ (prefixWord ++ tailWord_145472).sum := by decide
  have hdescent : baseEnd_145472 < baseStart_145472 := by decide
  rcases family_descends (prefixWord ++ tailWord_145472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145546 : List Nat := [3, 1, 2, 3, 1, 4, 2, 3]
def baseStart_145546 : Nat := 118140960795 + 145546 * 2 ^ 59
def prefixEnd_145546 : Nat := 4983230072969 + 3 ^ 40 * 145546 * 2
def baseEnd_145546 : Nat := 44287440201121649958905

theorem tailTrace_145546 : CollatzResearch.WordTrace tailWord_145546 prefixEnd_145546 44287440201121649958905 := by
  unfold tailWord_145546
  simp only [CollatzResearch.WordTrace]
  refine ⟨1327124682679793530730123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3538999153812782748613661 1327124682679793530730123)
  ·
    refine ⟨1990687024019690296095185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1327124682679793530730123 1990687024019690296095185)
    ·
      refine ⟨1493015268014767722071389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1990687024019690296095185 1493015268014767722071389)
      ·
        refine ⟨559880725505537895776771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1493015268014767722071389 559880725505537895776771)
        ·
          refine ⟨839821088258306843665157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 559880725505537895776771 839821088258306843665157)
          ·
            refine ⟨157466454048432533187217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 839821088258306843665157 157466454048432533187217)
            ·
              refine ⟨118099840536324399890413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157466454048432533187217 118099840536324399890413)
              ·
                refine ⟨44287440201121649958905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118099840536324399890413 44287440201121649958905)
                ·
                  rfl

theorem cell19_145546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_145546 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_145546 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_145546 prefixEnd_145546 := by exact prefixLift 145546
  have htrace : WordTrace (prefixWord ++ tailWord_145546) baseStart_145546 baseEnd_145546 := by
    simpa [prefixWord, tailWord_145546, baseEnd_145546] using wordTrace_append hprefix tailTrace_145546
  have hstable : (prefixWord ++ tailWord_145546).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145546).length < 2 ^ (prefixWord ++ tailWord_145546).sum := by decide
  have hdescent : baseEnd_145546 < baseStart_145546 := by decide
  rcases family_descends (prefixWord ++ tailWord_145546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145567 : List Nat := [1, 1, 2, 6, 1, 3, 5]
def baseStart_145567 : Nat := 118140960795 + 145567 * 2 ^ 59
def prefixEnd_145567 : Nat := 4983230072969 + 3 ^ 40 * 145567 * 2
def baseEnd_145567 : Nat := 14764610060866607830727

theorem tailTrace_145567 : CollatzResearch.WordTrace tailWord_145567 prefixEnd_145567 14764610060866607830727 := by
  unfold tailWord_145567
  simp only [CollatzResearch.WordTrace]
  refine ⟨5309264663643094709434955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3539509775762063139623303 5309264663643094709434955)
  ·
    refine ⟨7963896995464642064152433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5309264663643094709434955 7963896995464642064152433)
    ·
      refine ⟨5972922746598481548114325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7963896995464642064152433 5972922746598481548114325)
      ·
        refine ⟨279980753746803822567859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5972922746598481548114325 279980753746803822567859)
        ·
          refine ⟨419971130620205733851789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279980753746803822567859 419971130620205733851789)
          ·
            refine ⟨157489173982577150194421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 419971130620205733851789 157489173982577150194421)
            ·
              refine ⟨14764610060866607830727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 157489173982577150194421 14764610060866607830727)
              ·
                rfl

theorem cell19_145567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 5].length) (baseStart_145567 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_145567 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_145567 prefixEnd_145567 := by exact prefixLift 145567
  have htrace : WordTrace (prefixWord ++ tailWord_145567) baseStart_145567 baseEnd_145567 := by
    simpa [prefixWord, tailWord_145567, baseEnd_145567] using wordTrace_append hprefix tailTrace_145567
  have hstable : (prefixWord ++ tailWord_145567).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145567).length < 2 ^ (prefixWord ++ tailWord_145567).sum := by decide
  have hdescent : baseEnd_145567 < baseStart_145567 := by decide
  rcases family_descends (prefixWord ++ tailWord_145567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145569 : List Nat := [1, 2, 3, 3, 1, 2, 7]
def baseStart_145569 : Nat := 118140960795 + 145569 * 2 ^ 59
def prefixEnd_145569 : Nat := 4983230072969 + 3 ^ 40 * 145569 * 2
def baseEnd_145569 : Nat := 14764812917421470482577

theorem tailTrace_145569 : CollatzResearch.WordTrace tailWord_145569 prefixEnd_145569 14764812917421470482577 := by
  unfold tailWord_145569
  simp only [CollatzResearch.WordTrace]
  refine ⟨5309337609635849051007761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3539558406423899367338507 5309337609635849051007761)
  ·
    refine ⟨3982003207226886788255821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5309337609635849051007761 3982003207226886788255821)
    ·
      refine ⟨1493251202710082545595933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3982003207226886788255821 1493251202710082545595933)
      ·
        refine ⟨559969201016280954598475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1493251202710082545595933 559969201016280954598475)
        ·
          refine ⟨839953801524421431897713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 559969201016280954598475 839953801524421431897713)
          ·
            refine ⟨629965351143316073923285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 839953801524421431897713 629965351143316073923285)
            ·
              refine ⟨14764812917421470482577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 629965351143316073923285 14764812917421470482577)
              ·
                rfl

theorem cell19_145569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 7].length) (baseStart_145569 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_145569 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_145569 prefixEnd_145569 := by exact prefixLift 145569
  have htrace : WordTrace (prefixWord ++ tailWord_145569) baseStart_145569 baseEnd_145569 := by
    simpa [prefixWord, tailWord_145569, baseEnd_145569] using wordTrace_append hprefix tailTrace_145569
  have hstable : (prefixWord ++ tailWord_145569).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145569).length < 2 ^ (prefixWord ++ tailWord_145569).sum := by decide
  have hdescent : baseEnd_145569 < baseStart_145569 := by decide
  rcases family_descends (prefixWord ++ tailWord_145569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145582 : List Nat := [4, 1, 4, 2, 1, 1, 2, 4]
def baseStart_145582 : Nat := 118140960795 + 145582 * 2 ^ 59
def prefixEnd_145582 : Nat := 4983230072969 + 3 ^ 40 * 145582 * 2
def baseEnd_145582 : Nat := 44298394455084233158807

theorem tailTrace_145582 : CollatzResearch.WordTrace tailWord_145582 prefixEnd_145582 44298394455084233158807 := by
  unfold tailWord_145582
  simp only [CollatzResearch.WordTrace]
  refine ⟨663726469823594033903875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3539874505725834847487333 663726469823594033903875)
  ·
    refine ⟨995589704735391050855813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 663726469823594033903875 995589704735391050855813)
    ·
      refine ⟨186673069637885822035465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 995589704735391050855813 186673069637885822035465)
      ·
        refine ⟨140004802228414366526599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186673069637885822035465 140004802228414366526599)
        ·
          refine ⟨210007203342621549789899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140004802228414366526599 210007203342621549789899)
          ·
            refine ⟨315010805013932324684849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210007203342621549789899 315010805013932324684849)
            ·
              refine ⟨236258103760449243513637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 315010805013932324684849 236258103760449243513637)
              ·
                refine ⟨44298394455084233158807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 236258103760449243513637 44298394455084233158807)
                ·
                  rfl

theorem cell19_145582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_145582 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_145582 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_145582 prefixEnd_145582 := by exact prefixLift 145582
  have htrace : WordTrace (prefixWord ++ tailWord_145582) baseStart_145582 baseEnd_145582 := by
    simpa [prefixWord, tailWord_145582, baseEnd_145582] using wordTrace_append hprefix tailTrace_145582
  have hstable : (prefixWord ++ tailWord_145582).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145582).length < 2 ^ (prefixWord ++ tailWord_145582).sum := by decide
  have hdescent : baseEnd_145582 < baseStart_145582 := by decide
  rcases family_descends (prefixWord ++ tailWord_145582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145778 : List Nat := [3, 2, 1, 2, 1, 3, 2, 5]
def baseStart_145778 : Nat := 118140960795 + 145778 * 2 ^ 59
def prefixEnd_145778 : Nat := 4983230072969 + 3 ^ 40 * 145778 * 2
def baseEnd_145778 : Nat := 44358034282213852802717

theorem tailTrace_145778 : CollatzResearch.WordTrace tailWord_145778 prefixEnd_145778 44358034282213852802717 := by
  unfold tailWord_145778
  simp only [CollatzResearch.WordTrace]
  refine ⟨1329240116469669436341497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3544640310585785163577325 1329240116469669436341497)
  ·
    refine ⟨996930087352252077256123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1329240116469669436341497 996930087352252077256123)
    ·
      refine ⟨1495395131028378115884185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 996930087352252077256123 1495395131028378115884185)
      ·
        refine ⟨1121546348271283586913139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1495395131028378115884185 1121546348271283586913139)
        ·
          refine ⟨1682319522406925380369709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1121546348271283586913139 1682319522406925380369709)
          ·
            refine ⟨630869820902597017638641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1682319522406925380369709 630869820902597017638641)
            ·
              refine ⟨473152365676947763228981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 630869820902597017638641 473152365676947763228981)
              ·
                refine ⟨44358034282213852802717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 473152365676947763228981 44358034282213852802717)
                ·
                  rfl

theorem cell19_145778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_145778 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_145778 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_145778 prefixEnd_145778 := by exact prefixLift 145778
  have htrace : WordTrace (prefixWord ++ tailWord_145778) baseStart_145778 baseEnd_145778 := by
    simpa [prefixWord, tailWord_145778, baseEnd_145778] using wordTrace_append hprefix tailTrace_145778
  have hstable : (prefixWord ++ tailWord_145778).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145778).length < 2 ^ (prefixWord ++ tailWord_145778).sum := by decide
  have hdescent : baseEnd_145778 < baseStart_145778 := by decide
  rcases family_descends (prefixWord ++ tailWord_145778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145812 : List Nat := [2, 4, 2, 1, 3, 2, 1, 4]
def baseStart_145812 : Nat := 118140960795 + 145812 * 2 ^ 59
def prefixEnd_145812 : Nat := 4983230072969 + 3 ^ 40 * 145812 * 2
def baseEnd_145812 : Nat := 44368379966511848047069

theorem tailTrace_145812 : CollatzResearch.WordTrace tailWord_145812 prefixEnd_145812 44368379966511848047069 := by
  unfold tailWord_145812
  simp only [CollatzResearch.WordTrace]
  refine ⟨2659100273877750776051845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3545467031837001034735793 2659100273877750776051845)
  ·
    refine ⟨498581301352078270509721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2659100273877750776051845 498581301352078270509721)
    ·
      refine ⟨373935976014058702882291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 498581301352078270509721 373935976014058702882291)
      ·
        refine ⟨560903964021088054323437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373935976014058702882291 560903964021088054323437)
        ·
          refine ⟨210338986507908020371289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 560903964021088054323437 210338986507908020371289)
          ·
            refine ⟨157754239880931015278467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210338986507908020371289 157754239880931015278467)
            ·
              refine ⟨236631359821396522917701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157754239880931015278467 236631359821396522917701)
              ·
                refine ⟨44368379966511848047069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 236631359821396522917701 44368379966511848047069)
                ·
                  rfl

theorem cell19_145812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 4].length) (baseStart_145812 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_145812 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_145812 prefixEnd_145812 := by exact prefixLift 145812
  have htrace : WordTrace (prefixWord ++ tailWord_145812) baseStart_145812 baseEnd_145812 := by
    simpa [prefixWord, tailWord_145812, baseEnd_145812] using wordTrace_append hprefix tailTrace_145812
  have hstable : (prefixWord ++ tailWord_145812).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145812).length < 2 ^ (prefixWord ++ tailWord_145812).sum := by decide
  have hdescent : baseEnd_145812 < baseStart_145812 := by decide
  rcases family_descends (prefixWord ++ tailWord_145812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145913 : List Nat := [1, 2, 1, 3, 1, 2, 9]
def baseStart_145913 : Nat := 118140960795 + 145913 * 2 ^ 59
def prefixEnd_145913 : Nat := 4983230072969 + 3 ^ 40 * 145913 * 2
def baseEnd_145913 : Nat := 14799704244857846600783

theorem tailTrace_145913 : CollatzResearch.WordTrace tailWord_145913 prefixEnd_145913 14799704244857846600783 := by
  unfold tailWord_145913
  simp only [CollatzResearch.WordTrace]
  refine ⟨5321884320389595801530393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3547922880259730534353595 5321884320389595801530393)
  ·
    refine ⟨3991413240292196851147795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5321884320389595801530393 3991413240292196851147795)
    ·
      refine ⟨5987119860438295276721693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3991413240292196851147795 5987119860438295276721693)
      ·
        refine ⟨2245169947664360728770635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5987119860438295276721693 2245169947664360728770635)
        ·
          refine ⟨3367754921496541093155953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2245169947664360728770635 3367754921496541093155953)
          ·
            refine ⟨2525816191122405819866965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3367754921496541093155953 2525816191122405819866965)
            ·
              refine ⟨14799704244857846600783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2525816191122405819866965 14799704244857846600783)
              ·
                rfl

theorem cell19_145913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 9].length) (baseStart_145913 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_145913 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_145913 prefixEnd_145913 := by exact prefixLift 145913
  have htrace : WordTrace (prefixWord ++ tailWord_145913) baseStart_145913 baseEnd_145913 := by
    simpa [prefixWord, tailWord_145913, baseEnd_145913] using wordTrace_append hprefix tailTrace_145913
  have hstable : (prefixWord ++ tailWord_145913).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145913).length < 2 ^ (prefixWord ++ tailWord_145913).sum := by decide
  have hdescent : baseEnd_145913 < baseStart_145913 := by decide
  rcases family_descends (prefixWord ++ tailWord_145913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145930 : List Nat := [3, 1, 2, 2, 2, 1, 4, 4]
def baseStart_145930 : Nat := 118140960795 + 145930 * 2 ^ 59
def prefixEnd_145930 : Nat := 4983230072969 + 3 ^ 40 * 145930 * 2
def baseEnd_145930 : Nat := 44404285576722537424525

theorem tailTrace_145930 : CollatzResearch.WordTrace tailWord_145930 prefixEnd_145930 44404285576722537424525 := by
  unfold tailWord_145930
  simp only [CollatzResearch.WordTrace]
  refine ⟨1330626090332001926224811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3548336240885338469932829 1330626090332001926224811)
  ·
    refine ⟨1995939135498002889337217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1330626090332001926224811 1995939135498002889337217)
    ·
      refine ⟨1496954351623502167002913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1995939135498002889337217 1496954351623502167002913)
      ·
        refine ⟨1122715763717626625252185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1496954351623502167002913 1122715763717626625252185)
        ·
          refine ⟨842036822788219968939139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1122715763717626625252185 842036822788219968939139)
          ·
            refine ⟨1263055234182329953408709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 842036822788219968939139 1263055234182329953408709)
            ·
              refine ⟨236822856409186866264133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1263055234182329953408709 236822856409186866264133)
              ·
                refine ⟨44404285576722537424525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 236822856409186866264133 44404285576722537424525)
                ·
                  rfl

theorem cell19_145930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_145930 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_145930 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_145930 prefixEnd_145930 := by exact prefixLift 145930
  have htrace : WordTrace (prefixWord ++ tailWord_145930) baseStart_145930 baseEnd_145930 := by
    simpa [prefixWord, tailWord_145930, baseEnd_145930] using wordTrace_append hprefix tailTrace_145930
  have hstable : (prefixWord ++ tailWord_145930).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145930).length < 2 ^ (prefixWord ++ tailWord_145930).sum := by decide
  have hdescent : baseEnd_145930 < baseStart_145930 := by decide
  rcases family_descends (prefixWord ++ tailWord_145930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145949 : List Nat := [1, 4, 2, 2, 1, 2, 2, 5]
def baseStart_145949 : Nat := 118140960795 + 145949 * 2 ^ 59
def prefixEnd_145949 : Nat := 4983230072969 + 3 ^ 40 * 145949 * 2
def baseEnd_145949 : Nat := 44410066988536123002251

theorem tailTrace_145949 : CollatzResearch.WordTrace tailWord_145949 prefixEnd_145949 44410066988536123002251 := by
  unfold tailWord_145949
  simp only [CollatzResearch.WordTrace]
  refine ⟨5323197348259173949840901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3548798232172782633227267 5323197348259173949840901)
  ·
    refine ⟨998099502798595115595169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5323197348259173949840901 998099502798595115595169)
    ·
      refine ⟨748574627098946336696377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 998099502798595115595169 748574627098946336696377)
      ·
        refine ⟨561430970324209752522283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 748574627098946336696377 561430970324209752522283)
        ·
          refine ⟨842146455486314628783425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 561430970324209752522283 842146455486314628783425)
          ·
            refine ⟨631609841614735971587569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 842146455486314628783425 631609841614735971587569)
            ·
              refine ⟨473707381211051978690677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 631609841614735971587569 473707381211051978690677)
              ·
                refine ⟨44410066988536123002251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 473707381211051978690677 44410066988536123002251)
                ·
                  rfl

theorem cell19_145949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 5].length) (baseStart_145949 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_145949 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_145949 prefixEnd_145949 := by exact prefixLift 145949
  have htrace : WordTrace (prefixWord ++ tailWord_145949) baseStart_145949 baseEnd_145949 := by
    simpa [prefixWord, tailWord_145949, baseEnd_145949] using wordTrace_append hprefix tailTrace_145949
  have hstable : (prefixWord ++ tailWord_145949).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145949).length < 2 ^ (prefixWord ++ tailWord_145949).sum := by decide
  have hdescent : baseEnd_145949 < baseStart_145949 := by decide
  rcases family_descends (prefixWord ++ tailWord_145949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145966 : List Nat := [4, 1, 3, 1, 4, 6]
def baseStart_145966 : Nat := 118140960795 + 145966 * 2 ^ 59
def prefixEnd_145966 : Nat := 4983230072969 + 3 ^ 40 * 145966 * 2
def baseEnd_145966 : Nat := 4935026647853902291603

theorem tailTrace_145966 : CollatzResearch.WordTrace tailWord_145966 prefixEnd_145966 4935026647853902291603 := by
  unfold tailWord_145966
  simp only [CollatzResearch.WordTrace]
  refine ⟨665477173649698231651219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3549211592798390568806501 665477173649698231651219)
  ·
    refine ⟨998215760474547347476829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 665477173649698231651219 998215760474547347476829)
    ·
      refine ⟨374330910177955255303811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 998215760474547347476829 374330910177955255303811)
      ·
        refine ⟨561496365266932882955717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374330910177955255303811 561496365266932882955717)
        ·
          refine ⟨105280568487549915554197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 561496365266932882955717 105280568487549915554197)
          ·
            refine ⟨4935026647853902291603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 105280568487549915554197 4935026647853902291603)
            ·
              rfl

theorem cell19_145966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 6].length) (baseStart_145966 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_145966 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_145966 prefixEnd_145966 := by exact prefixLift 145966
  have htrace : WordTrace (prefixWord ++ tailWord_145966) baseStart_145966 baseEnd_145966 := by
    simpa [prefixWord, tailWord_145966, baseEnd_145966] using wordTrace_append hprefix tailTrace_145966
  have hstable : (prefixWord ++ tailWord_145966).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145966).length < 2 ^ (prefixWord ++ tailWord_145966).sum := by decide
  have hdescent : baseEnd_145966 < baseStart_145966 := by decide
  rcases family_descends (prefixWord ++ tailWord_145966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145985 : List Nat := [1, 2, 5, 1, 1, 4, 1, 4]
def baseStart_145985 : Nat := 118140960795 + 145985 * 2 ^ 59
def prefixEnd_145985 : Nat := 4983230072969 + 3 ^ 40 * 145985 * 2
def baseEnd_145985 : Nat := 44421021242498706202153

theorem tailTrace_145985 : CollatzResearch.WordTrace tailWord_145985 prefixEnd_145985 44421021242498706202153 := by
  unfold tailWord_145985
  simp only [CollatzResearch.WordTrace]
  refine ⟨5324510376128752098151409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3549673584085834732100939 5324510376128752098151409)
  ·
    refine ⟨3993382782096564073613557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5324510376128752098151409 3993382782096564073613557)
    ·
      refine ⟨374379635821552881901271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3993382782096564073613557 374379635821552881901271)
      ·
        refine ⟨561569453732329322851907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374379635821552881901271 561569453732329322851907)
        ·
          refine ⟨842354180598493984277861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 561569453732329322851907 842354180598493984277861)
          ·
            refine ⟨157941408862217622052099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 842354180598493984277861 157941408862217622052099)
            ·
              refine ⟨236912113293326433078149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157941408862217622052099 236912113293326433078149)
              ·
                refine ⟨44421021242498706202153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 236912113293326433078149 44421021242498706202153)
                ·
                  rfl

theorem cell19_145985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 4].length) (baseStart_145985 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_145985 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_145985 prefixEnd_145985 := by exact prefixLift 145985
  have htrace : WordTrace (prefixWord ++ tailWord_145985) baseStart_145985 baseEnd_145985 := by
    simpa [prefixWord, tailWord_145985, baseEnd_145985] using wordTrace_append hprefix tailTrace_145985
  have hstable : (prefixWord ++ tailWord_145985).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145985).length < 2 ^ (prefixWord ++ tailWord_145985).sum := by decide
  have hdescent : baseEnd_145985 < baseStart_145985 := by decide
  rcases family_descends (prefixWord ++ tailWord_145985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146004 : List Nat := [2, 4, 1, 1, 1, 4, 3, 3]
def baseStart_146004 : Nat := 118140960795 + 146004 * 2 ^ 59
def prefixEnd_146004 : Nat := 4983230072969 + 3 ^ 40 * 146004 * 2
def baseEnd_146004 : Nat := 44426802654312291779879

theorem tailTrace_146004 : CollatzResearch.WordTrace tailWord_146004 prefixEnd_146004 44426802654312291779879 := by
  unfold tailWord_146004
  simp only [CollatzResearch.WordTrace]
  refine ⟨2662601681529959171546533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3550135575373278895395377 2662601681529959171546533)
  ·
    refine ⟨499237815286867344664975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2662601681529959171546533 499237815286867344664975)
    ·
      refine ⟨748856722930301016997463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 499237815286867344664975 748856722930301016997463)
      ·
        refine ⟨1123285084395451525496195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 748856722930301016997463 1123285084395451525496195)
        ·
          refine ⟨1684927626593177288244293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1123285084395451525496195 1684927626593177288244293)
          ·
            refine ⟨315923929986220741545805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1684927626593177288244293 315923929986220741545805)
            ·
              refine ⟨118471473744832778079677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 315923929986220741545805 118471473744832778079677)
              ·
                refine ⟨44426802654312291779879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118471473744832778079677 44426802654312291779879)
                ·
                  rfl

theorem cell19_146004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 3].length) (baseStart_146004 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_146004 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_146004 prefixEnd_146004 := by exact prefixLift 146004
  have htrace : WordTrace (prefixWord ++ tailWord_146004) baseStart_146004 baseEnd_146004 := by
    simpa [prefixWord, tailWord_146004, baseEnd_146004] using wordTrace_append hprefix tailTrace_146004
  have hstable : (prefixWord ++ tailWord_146004).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146004).length < 2 ^ (prefixWord ++ tailWord_146004).sum := by decide
  have hdescent : baseEnd_146004 < baseStart_146004 := by decide
  rcases family_descends (prefixWord ++ tailWord_146004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146008 : List Nat := [2, 1, 2, 2, 1, 2, 2, 7]
def baseStart_146008 : Nat := 118140960795 + 146008 * 2 ^ 59
def prefixEnd_146008 : Nat := 4983230072969 + 3 ^ 40 * 146008 * 2
def baseEnd_146008 : Nat := 44428019793641467690979

theorem tailTrace_146008 : CollatzResearch.WordTrace tailWord_146008 prefixEnd_146008 44428019793641467690979 := by
  unfold tailWord_146008
  simp only [CollatzResearch.WordTrace]
  refine ⟨2662674627522713513119339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3550232836696951350825785 2662674627522713513119339)
  ·
    refine ⟨3994011941284070269679009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2662674627522713513119339 3994011941284070269679009)
    ·
      refine ⟨2995508955963052702259257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3994011941284070269679009 2995508955963052702259257)
      ·
        refine ⟨2246631716972289526694443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2995508955963052702259257 2246631716972289526694443)
        ·
          refine ⟨3369947575458434290041665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2246631716972289526694443 3369947575458434290041665)
          ·
            refine ⟨2527460681593825717531249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3369947575458434290041665 2527460681593825717531249)
            ·
              refine ⟨1895595511195369288148437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2527460681593825717531249 1895595511195369288148437)
              ·
                refine ⟨44428019793641467690979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1895595511195369288148437 44428019793641467690979)
                ·
                  rfl

theorem cell19_146008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_146008 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_146008 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_146008 prefixEnd_146008 := by exact prefixLift 146008
  have htrace : WordTrace (prefixWord ++ tailWord_146008) baseStart_146008 baseEnd_146008 := by
    simpa [prefixWord, tailWord_146008, baseEnd_146008] using wordTrace_append hprefix tailTrace_146008
  have hstable : (prefixWord ++ tailWord_146008).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146008).length < 2 ^ (prefixWord ++ tailWord_146008).sum := by decide
  have hdescent : baseEnd_146008 < baseStart_146008 := by decide
  rcases family_descends (prefixWord ++ tailWord_146008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146080 : List Nat := [2, 1, 1, 4, 5, 1, 5]
def baseStart_146080 : Nat := 118140960795 + 146080 * 2 ^ 59
def prefixEnd_146080 : Nat := 4983230072969 + 3 ^ 40 * 146080 * 2
def baseEnd_146080 : Nat := 14816642767188878030261

theorem tailTrace_146080 : CollatzResearch.WordTrace tailWord_146080 prefixEnd_146080 14816642767188878030261 := by
  unfold tailWord_146080
  simp only [CollatzResearch.WordTrace]
  refine ⟨2663987655392291661429847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3551983540523055548573129 2663987655392291661429847)
  ·
    refine ⟨3995981483088437492144771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2663987655392291661429847 3995981483088437492144771)
    ·
      refine ⟨5993972224632656238217157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3995981483088437492144771 5993972224632656238217157)
      ·
        refine ⟨1123869792118623044665717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5993972224632656238217157 1123869792118623044665717)
        ·
          refine ⟨105362793011120910437411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1123869792118623044665717 105362793011120910437411)
          ·
            refine ⟨158044189516681365656117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105362793011120910437411 158044189516681365656117)
            ·
              refine ⟨14816642767188878030261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 158044189516681365656117 14816642767188878030261)
              ·
                rfl

theorem cell19_146080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 5].length) (baseStart_146080 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_146080 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_146080 prefixEnd_146080 := by exact prefixLift 146080
  have htrace : WordTrace (prefixWord ++ tailWord_146080) baseStart_146080 baseEnd_146080 := by
    simpa [prefixWord, tailWord_146080, baseEnd_146080] using wordTrace_append hprefix tailTrace_146080
  have hstable : (prefixWord ++ tailWord_146080).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146080).length < 2 ^ (prefixWord ++ tailWord_146080).sum := by decide
  have hdescent : baseEnd_146080 < baseStart_146080 := by decide
  rcases family_descends (prefixWord ++ tailWord_146080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146101 : List Nat := [1, 3, 3, 3, 1, 1, 1, 6]
def baseStart_146101 : Nat := 118140960795 + 146101 * 2 ^ 59
def prefixEnd_146101 : Nat := 4983230072969 + 3 ^ 40 * 146101 * 2
def baseEnd_146101 : Nat := 44456318283044807624059

theorem tailTrace_146101 : CollatzResearch.WordTrace tailWord_146101 prefixEnd_146101 44456318283044807624059 := by
  unfold tailWord_146101
  simp only [CollatzResearch.WordTrace]
  refine ⟨5328741243708503909374157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3552494162472335939582771 5328741243708503909374157)
  ·
    refine ⟨1998277966390688966015309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5328741243708503909374157 1998277966390688966015309)
    ·
      refine ⟨749354237396508362255741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1998277966390688966015309 749354237396508362255741)
      ·
        refine ⟨281007839023690635845903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 749354237396508362255741 281007839023690635845903)
        ·
          refine ⟨421511758535535953768855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281007839023690635845903 421511758535535953768855)
          ·
            refine ⟨632267637803303930653283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 421511758535535953768855 632267637803303930653283)
            ·
              refine ⟨948401456704955895979925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 632267637803303930653283 948401456704955895979925)
              ·
                refine ⟨44456318283044807624059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 948401456704955895979925 44456318283044807624059)
                ·
                  rfl

theorem cell19_146101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 6].length) (baseStart_146101 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_146101 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_146101 prefixEnd_146101 := by exact prefixLift 146101
  have htrace : WordTrace (prefixWord ++ tailWord_146101) baseStart_146101 baseEnd_146101 := by
    simpa [prefixWord, tailWord_146101, baseEnd_146101] using wordTrace_append hprefix tailTrace_146101
  have hstable : (prefixWord ++ tailWord_146101).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146101).length < 2 ^ (prefixWord ++ tailWord_146101).sum := by decide
  have hdescent : baseEnd_146101 < baseStart_146101 := by decide
  rcases family_descends (prefixWord ++ tailWord_146101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146141 : List Nat := [1, 4, 3, 11]
def baseStart_146141 : Nat := 118140960795 + 146141 * 2 ^ 59
def prefixEnd_146141 : Nat := 4983230072969 + 3 ^ 40 * 146141 * 2
def baseEnd_146141 : Nat := 548993699707858848581

theorem tailTrace_146141 : CollatzResearch.WordTrace tailWord_146141 prefixEnd_146141 548993699707858848581 := by
  unfold tailWord_146141
  simp only [CollatzResearch.WordTrace]
  refine ⟨5330200163563590740830277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3553466775709060493886851 5330200163563590740830277)
  ·
    refine ⟨999412530668173263905677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5330200163563590740830277 999412530668173263905677)
    ·
      refine ⟨374779699000564973964629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 999412530668173263905677 374779699000564973964629)
      ·
        refine ⟨548993699707858848581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 374779699000564973964629 548993699707858848581)
        ·
          rfl

theorem cell19_146141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 11].length) (baseStart_146141 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_146141 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_146141 prefixEnd_146141 := by exact prefixLift 146141
  have htrace : WordTrace (prefixWord ++ tailWord_146141) baseStart_146141 baseEnd_146141 := by
    simpa [prefixWord, tailWord_146141, baseEnd_146141] using wordTrace_append hprefix tailTrace_146141
  have hstable : (prefixWord ++ tailWord_146141).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146141).length < 2 ^ (prefixWord ++ tailWord_146141).sum := by decide
  have hdescent : baseEnd_146141 < baseStart_146141 := by decide
  rcases family_descends (prefixWord ++ tailWord_146141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146158 : List Nat := [4, 1, 2, 1, 1, 3, 3, 4]
def baseStart_146158 : Nat := 118140960795 + 146158 * 2 ^ 59
def prefixEnd_146158 : Nat := 4983230072969 + 3 ^ 40 * 146158 * 2
def baseEnd_146158 : Nat := 44473662518485564357237

theorem tailTrace_146158 : CollatzResearch.WordTrace tailWord_146158 prefixEnd_146158 44473662518485564357237 := by
  unfold tailWord_146158
  simp only [CollatzResearch.WordTrace]
  refine ⟨666352525562750330524891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3553880136334668429466085 666352525562750330524891)
  ·
    refine ⟨999528788344125495787337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 666352525562750330524891 999528788344125495787337)
    ·
      refine ⟨749646591258094121840503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 999528788344125495787337 749646591258094121840503)
      ·
        refine ⟨1124469886887141182760755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 749646591258094121840503 1124469886887141182760755)
        ·
          refine ⟨1686704830330711774141133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1124469886887141182760755 1686704830330711774141133)
          ·
            refine ⟨632514311374016915302925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1686704830330711774141133 632514311374016915302925)
            ·
              refine ⟨237192866765256343238597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 632514311374016915302925 237192866765256343238597)
              ·
                refine ⟨44473662518485564357237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 237192866765256343238597 44473662518485564357237)
                ·
                  rfl

theorem cell19_146158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_146158 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_146158 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_146158 prefixEnd_146158 := by exact prefixLift 146158
  have htrace : WordTrace (prefixWord ++ tailWord_146158) baseStart_146158 baseEnd_146158 := by
    simpa [prefixWord, tailWord_146158, baseEnd_146158] using wordTrace_append hprefix tailTrace_146158
  have hstable : (prefixWord ++ tailWord_146158).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146158).length < 2 ^ (prefixWord ++ tailWord_146158).sum := by decide
  have hdescent : baseEnd_146158 < baseStart_146158 := by decide
  rcases family_descends (prefixWord ++ tailWord_146158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146194 : List Nat := [3, 2, 4, 1, 2, 1, 6]
def baseStart_146194 : Nat := 118140960795 + 146194 * 2 ^ 59
def prefixEnd_146194 : Nat := 4983230072969 + 3 ^ 40 * 146194 * 2
def baseEnd_146194 : Nat := 14828205590816049185713

theorem tailTrace_146194 : CollatzResearch.WordTrace tailWord_146194 prefixEnd_146194 14828205590816049185713 := by
  unfold tailWord_146194
  simp only [CollatzResearch.WordTrace]
  refine ⟨1333033308092895198127409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3554755488247720528339757 1333033308092895198127409)
  ·
    refine ⟨999774981069671398595557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1333033308092895198127409 999774981069671398595557)
    ·
      refine ⟨187457808950563387236667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 999774981069671398595557 187457808950563387236667)
      ·
        refine ⟨281186713425845080855001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187457808950563387236667 281186713425845080855001)
        ·
          refine ⟨210890035069383810641251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 281186713425845080855001 210890035069383810641251)
          ·
            refine ⟨316335052604075715961877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210890035069383810641251 316335052604075715961877)
            ·
              refine ⟨14828205590816049185713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 316335052604075715961877 14828205590816049185713)
              ·
                rfl

theorem cell19_146194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 6].length) (baseStart_146194 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_146194 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_146194 prefixEnd_146194 := by exact prefixLift 146194
  have htrace : WordTrace (prefixWord ++ tailWord_146194) baseStart_146194 baseEnd_146194 := by
    simpa [prefixWord, tailWord_146194, baseEnd_146194] using wordTrace_append hprefix tailTrace_146194
  have hstable : (prefixWord ++ tailWord_146194).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146194).length < 2 ^ (prefixWord ++ tailWord_146194).sum := by decide
  have hdescent : baseEnd_146194 < baseStart_146194 := by decide
  rcases family_descends (prefixWord ++ tailWord_146194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146228 : List Nat := [2, 5, 1, 1, 4, 1, 2, 3]
def baseStart_146228 : Nat := 118140960795 + 146228 * 2 ^ 59
def prefixEnd_146228 : Nat := 4983230072969 + 3 ^ 40 * 146228 * 2
def baseEnd_146228 : Nat := 44494962456746142801491

theorem tailTrace_146228 : CollatzResearch.WordTrace tailWord_146228 prefixEnd_146228 44494962456746142801491 := by
  unfold tailWord_146228
  simp only [CollatzResearch.WordTrace]
  refine ⟨2666686657124202299623669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3555582209498936399498225 2666686657124202299623669)
  ·
    refine ⟨250001874105393965589719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2666686657124202299623669 250001874105393965589719)
    ·
      refine ⟨375002811158090948384579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 250001874105393965589719 375002811158090948384579)
      ·
        refine ⟨562504216737136422576869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375002811158090948384579 562504216737136422576869)
        ·
          refine ⟨105469540638213079233163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 562504216737136422576869 105469540638213079233163)
          ·
            refine ⟨158204310957319618849745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105469540638213079233163 158204310957319618849745)
            ·
              refine ⟨118653233217989714137309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158204310957319618849745 118653233217989714137309)
              ·
                refine ⟨44494962456746142801491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118653233217989714137309 44494962456746142801491)
                ·
                  rfl

theorem cell19_146228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 3].length) (baseStart_146228 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_146228 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_146228 prefixEnd_146228 := by exact prefixLift 146228
  have htrace : WordTrace (prefixWord ++ tailWord_146228) baseStart_146228 baseEnd_146228 := by
    simpa [prefixWord, tailWord_146228, baseEnd_146228] using wordTrace_append hprefix tailTrace_146228
  have hstable : (prefixWord ++ tailWord_146228).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146228).length < 2 ^ (prefixWord ++ tailWord_146228).sum := by decide
  have hdescent : baseEnd_146228 < baseStart_146228 := by decide
  rcases family_descends (prefixWord ++ tailWord_146228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146234 : List Nat := [3, 1, 1, 1, 6, 1, 1, 5]
def baseStart_146234 : Nat := 118140960795 + 146234 * 2 ^ 59
def prefixEnd_146234 : Nat := 4983230072969 + 3 ^ 40 * 146234 * 2
def baseEnd_146234 : Nat := 44496788165739906668141

theorem tailTrace_146234 : CollatzResearch.WordTrace tailWord_146234 prefixEnd_146234 44496788165739906668141 := by
  unfold tailWord_146234
  simp only [CollatzResearch.WordTrace]
  refine ⟨1333398038056666905991439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3555728101484445082643837 1333398038056666905991439)
  ·
    refine ⟨2000097057085000358987159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1333398038056666905991439 2000097057085000358987159)
    ·
      refine ⟨3000145585627500538480739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2000097057085000358987159 3000145585627500538480739)
      ·
        refine ⟨4500218378441250807721109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3000145585627500538480739 4500218378441250807721109)
        ·
          refine ⟨210947736489433631611927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4500218378441250807721109 210947736489433631611927)
          ·
            refine ⟨316421604734150447417891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210947736489433631611927 316421604734150447417891)
            ·
              refine ⟨474632407101225671126837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316421604734150447417891 474632407101225671126837)
              ·
                refine ⟨44496788165739906668141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 474632407101225671126837 44496788165739906668141)
                ·
                  rfl

theorem cell19_146234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_146234 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_146234 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_146234 prefixEnd_146234 := by exact prefixLift 146234
  have htrace : WordTrace (prefixWord ++ tailWord_146234) baseStart_146234 baseEnd_146234 := by
    simpa [prefixWord, tailWord_146234, baseEnd_146234] using wordTrace_append hprefix tailTrace_146234
  have hstable : (prefixWord ++ tailWord_146234).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146234).length < 2 ^ (prefixWord ++ tailWord_146234).sum := by decide
  have hdescent : baseEnd_146234 < baseStart_146234 := by decide
  rcases family_descends (prefixWord ++ tailWord_146234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146306 : List Nat := [3, 4, 2, 2, 2, 6]
def baseStart_146306 : Nat := 118140960795 + 146306 * 2 ^ 59
def prefixEnd_146306 : Nat := 4983230072969 + 3 ^ 40 * 146306 * 2
def baseEnd_146306 : Nat := 4946521852629452563105

theorem tailTrace_146306 : CollatzResearch.WordTrace tailWord_146306 prefixEnd_146306 4946521852629452563105 := by
  unfold tailWord_146306
  simp only [CollatzResearch.WordTrace]
  refine ⟨1334054551991455980146693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3557478805310549280391181 1334054551991455980146693)
  ·
    refine ⟨250135228498397996277505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1334054551991455980146693 250135228498397996277505)
    ·
      refine ⟨187601421373798497208129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 250135228498397996277505 187601421373798497208129)
      ·
        refine ⟨140701066030348872906097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187601421373798497208129 140701066030348872906097)
        ·
          refine ⟨105525799522761654679573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140701066030348872906097 105525799522761654679573)
          ·
            refine ⟨4946521852629452563105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 105525799522761654679573 4946521852629452563105)
            ·
              rfl

theorem cell19_146306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 6].length) (baseStart_146306 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_146306 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_146306 prefixEnd_146306 := by exact prefixLift 146306
  have htrace : WordTrace (prefixWord ++ tailWord_146306) baseStart_146306 baseEnd_146306 := by
    simpa [prefixWord, tailWord_146306, baseEnd_146306] using wordTrace_append hprefix tailTrace_146306
  have hstable : (prefixWord ++ tailWord_146306).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146306).length < 2 ^ (prefixWord ++ tailWord_146306).sum := by decide
  have hdescent : baseEnd_146306 < baseStart_146306 := by decide
  rcases family_descends (prefixWord ++ tailWord_146306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146312 : List Nat := [2, 1, 3, 3, 2, 8]
def baseStart_146312 : Nat := 118140960795 + 146312 * 2 ^ 59
def prefixEnd_146312 : Nat := 4983230072969 + 3 ^ 40 * 146312 * 2
def baseEnd_146312 : Nat := 4946724709184315214955

theorem tailTrace_146312 : CollatzResearch.WordTrace tailWord_146312 prefixEnd_146312 4946724709184315214955 := by
  unfold tailWord_146312
  simp only [CollatzResearch.WordTrace]
  refine ⟨2668218522972043472652595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3557624697296057963536793 2668218522972043472652595)
  ·
    refine ⟨4002327784458065208978893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2668218522972043472652595 4002327784458065208978893)
    ·
      refine ⟨1500872919171774453367085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4002327784458065208978893 1500872919171774453367085)
      ·
        refine ⟨562827344689415420012657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1500872919171774453367085 562827344689415420012657)
        ·
          refine ⟨422120508517061565009493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 562827344689415420012657 422120508517061565009493)
          ·
            refine ⟨4946724709184315214955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 422120508517061565009493 4946724709184315214955)
            ·
              rfl

theorem cell19_146312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 8].length) (baseStart_146312 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_146312 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_146312 prefixEnd_146312 := by exact prefixLift 146312
  have htrace : WordTrace (prefixWord ++ tailWord_146312) baseStart_146312 baseEnd_146312 := by
    simpa [prefixWord, tailWord_146312, baseEnd_146312] using wordTrace_append hprefix tailTrace_146312
  have hstable : (prefixWord ++ tailWord_146312).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146312).length < 2 ^ (prefixWord ++ tailWord_146312).sum := by decide
  have hdescent : baseEnd_146312 < baseStart_146312 := by decide
  rcases family_descends (prefixWord ++ tailWord_146312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146574 : List Nat := [4, 1, 1, 3, 2, 3, 2, 3]
def baseStart_146574 : Nat := 118140960795 + 146574 * 2 ^ 59
def prefixEnd_146574 : Nat := 4983230072969 + 3 ^ 40 * 146574 * 2
def baseEnd_146574 : Nat := 44600245008719859111659

theorem tailTrace_146574 : CollatzResearch.WordTrace tailWord_146574 prefixEnd_146574 44600245008719859111659 := by
  unfold tailWord_146574
  simp only [CollatzResearch.WordTrace]
  refine ⟨668249121374363211417847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3563995313996603794228517 668249121374363211417847)
  ·
    refine ⟨1002373682061544817126771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 668249121374363211417847 1002373682061544817126771)
    ·
      refine ⟨1503560523092317225690157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1002373682061544817126771 1503560523092317225690157)
      ·
        refine ⟨563835196159618959633809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1503560523092317225690157 563835196159618959633809)
        ·
          refine ⟨422876397119714219725357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 563835196159618959633809 422876397119714219725357)
          ·
            refine ⟨158578648919892832397009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 422876397119714219725357 158578648919892832397009)
            ·
              refine ⟨118933986689919624297757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158578648919892832397009 118933986689919624297757)
              ·
                refine ⟨44600245008719859111659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118933986689919624297757 44600245008719859111659)
                ·
                  rfl

theorem cell19_146574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_146574 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_146574 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_146574 prefixEnd_146574 := by exact prefixLift 146574
  have htrace : WordTrace (prefixWord ++ tailWord_146574) baseStart_146574 baseEnd_146574 := by
    simpa [prefixWord, tailWord_146574, baseEnd_146574] using wordTrace_append hprefix tailTrace_146574
  have hstable : (prefixWord ++ tailWord_146574).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146574).length < 2 ^ (prefixWord ++ tailWord_146574).sum := by decide
  have hdescent : baseEnd_146574 < baseStart_146574 := by decide
  rcases family_descends (prefixWord ++ tailWord_146574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146597 : List Nat := [1, 3, 1, 2, 1, 6, 5]
def baseStart_146597 : Nat := 118140960795 + 146597 * 2 ^ 59
def prefixEnd_146597 : Nat := 4983230072969 + 3 ^ 40 * 146597 * 2
def baseEnd_146597 : Nat := 14869081186620873533495

theorem tailTrace_146597 : CollatzResearch.WordTrace tailWord_146597 prefixEnd_146597 14869081186620873533495 := by
  unfold tailWord_146597
  simp only [CollatzResearch.WordTrace]
  refine ⟨5346831849911580619430045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3564554566607720412953363 5346831849911580619430045)
  ·
    refine ⟨2005061943716842732286267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5346831849911580619430045 2005061943716842732286267)
    ·
      refine ⟨3007592915575264098429401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2005061943716842732286267 3007592915575264098429401)
      ·
        refine ⟨2255694686681448073822051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3007592915575264098429401 2255694686681448073822051)
        ·
          refine ⟨3383542030022172110733077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2255694686681448073822051 3383542030022172110733077)
          ·
            refine ⟨158603532657289317690613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3383542030022172110733077 158603532657289317690613)
            ·
              refine ⟨14869081186620873533495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 158603532657289317690613 14869081186620873533495)
              ·
                rfl

theorem cell19_146597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 5].length) (baseStart_146597 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_146597 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_146597 prefixEnd_146597 := by exact prefixLift 146597
  have htrace : WordTrace (prefixWord ++ tailWord_146597) baseStart_146597 baseEnd_146597 := by
    simpa [prefixWord, tailWord_146597, baseEnd_146597] using wordTrace_append hprefix tailTrace_146597
  have hstable : (prefixWord ++ tailWord_146597).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146597).length < 2 ^ (prefixWord ++ tailWord_146597).sum := by decide
  have hdescent : baseEnd_146597 < baseStart_146597 := by decide
  rcases family_descends (prefixWord ++ tailWord_146597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146656 : List Nat := [2, 1, 1, 3, 1, 11]
def baseStart_146656 : Nat := 118140960795 + 146656 * 2 ^ 59
def prefixEnd_146656 : Nat := 4983230072969 + 3 ^ 40 * 146656 * 2
def baseEnd_146656 : Nat := 4958355151663107254357

theorem tailTrace_146656 : CollatzResearch.WordTrace tailWord_146656 prefixEnd_146656 4958355151663107254357 := by
  unfold tailWord_146656
  simp only [CollatzResearch.WordTrace]
  refine ⟨2674491878348916847913911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3565989171131889130551881 2674491878348916847913911)
  ·
    refine ⟨4011737817523375271870867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2674491878348916847913911 4011737817523375271870867)
    ·
      refine ⟨6017606726285062907806301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4011737817523375271870867 6017606726285062907806301)
      ·
        refine ⟨2256602522356898590427363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6017606726285062907806301 2256602522356898590427363)
        ·
          refine ⟨3384903783535347885641045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2256602522356898590427363 3384903783535347885641045)
          ·
            refine ⟨4958355151663107254357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3384903783535347885641045 4958355151663107254357)
            ·
              rfl

theorem cell19_146656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 11].length) (baseStart_146656 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_146656 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_146656 prefixEnd_146656 := by exact prefixLift 146656
  have htrace : WordTrace (prefixWord ++ tailWord_146656) baseStart_146656 baseEnd_146656 := by
    simpa [prefixWord, tailWord_146656, baseEnd_146656] using wordTrace_append hprefix tailTrace_146656
  have hstable : (prefixWord ++ tailWord_146656).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146656).length < 2 ^ (prefixWord ++ tailWord_146656).sum := by decide
  have hdescent : baseEnd_146656 < baseStart_146656 := by decide
  rcases family_descends (prefixWord ++ tailWord_146656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146671 : List Nat := [1, 1, 2, 1, 7, 2, 1, 4]
def baseStart_146671 : Nat := 118140960795 + 146671 * 2 ^ 59
def prefixEnd_146671 : Nat := 4983230072969 + 3 ^ 40 * 146671 * 2
def baseEnd_146671 : Nat := 44629760637452374955839

theorem tailTrace_146671 : CollatzResearch.WordTrace tailWord_146671 prefixEnd_146671 44629760637452374955839 := by
  unfold tailWord_146671
  simp only [CollatzResearch.WordTrace]
  refine ⟨5349530851643491257623867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3566353901095660838415911 5349530851643491257623867)
  ·
    refine ⟨8024296277465236886435801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5349530851643491257623867 8024296277465236886435801)
    ·
      refine ⟨6018222208098927664826851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8024296277465236886435801 6018222208098927664826851)
      ·
        refine ⟨9027333312148391497240277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6018222208098927664826851 9027333312148391497240277)
        ·
          refine ⟨211578124503477925716569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 9027333312148391497240277 211578124503477925716569)
          ·
            refine ⟨158683593377608444287427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211578124503477925716569 158683593377608444287427)
            ·
              refine ⟨238025390066412666431141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158683593377608444287427 238025390066412666431141)
              ·
                refine ⟨44629760637452374955839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 238025390066412666431141 44629760637452374955839)
                ·
                  rfl

theorem cell19_146671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 4].length) (baseStart_146671 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_146671 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_146671 prefixEnd_146671 := by exact prefixLift 146671
  have htrace : WordTrace (prefixWord ++ tailWord_146671) baseStart_146671 baseEnd_146671 := by
    simpa [prefixWord, tailWord_146671, baseEnd_146671] using wordTrace_append hprefix tailTrace_146671
  have hstable : (prefixWord ++ tailWord_146671).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146671).length < 2 ^ (prefixWord ++ tailWord_146671).sum := by decide
  have hdescent : baseEnd_146671 < baseStart_146671 := by decide
  rcases family_descends (prefixWord ++ tailWord_146671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146732 : List Nat := [2, 2, 1, 1, 1, 3, 1, 8]
def baseStart_146732 : Nat := 118140960795 + 146732 * 2 ^ 59
def prefixEnd_146732 : Nat := 4983230072969 + 3 ^ 40 * 146732 * 2
def baseEnd_146732 : Nat := 44648322012222307600117

theorem tailTrace_146732 : CollatzResearch.WordTrace tailWord_146732 prefixEnd_146732 44648322012222307600117 := by
  unfold tailWord_146732
  simp only [CollatzResearch.WordTrace]
  refine ⟨2675877852211249337797225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3567837136281665783729633 2675877852211249337797225)
  ·
    refine ⟨2006908389158437003347919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2675877852211249337797225 2006908389158437003347919)
    ·
      refine ⟨3010362583737655505021879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2006908389158437003347919 3010362583737655505021879)
      ·
        refine ⟨4515543875606483257532819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3010362583737655505021879 4515543875606483257532819)
        ·
          refine ⟨6773315813409724886299229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4515543875606483257532819 6773315813409724886299229)
          ·
            refine ⟨2539993430028646832362211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6773315813409724886299229 2539993430028646832362211)
            ·
              refine ⟨3809990145042970248543317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2539993430028646832362211 3809990145042970248543317)
              ·
                refine ⟨44648322012222307600117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3809990145042970248543317 44648322012222307600117)
                ·
                  rfl

theorem cell19_146732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_146732 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_146732 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_146732 prefixEnd_146732 := by exact prefixLift 146732
  have htrace : WordTrace (prefixWord ++ tailWord_146732) baseStart_146732 baseEnd_146732 := by
    simpa [prefixWord, tailWord_146732, baseEnd_146732] using wordTrace_append hprefix tailTrace_146732
  have hstable : (prefixWord ++ tailWord_146732).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146732).length < 2 ^ (prefixWord ++ tailWord_146732).sum := by decide
  have hdescent : baseEnd_146732 < baseStart_146732 := by decide
  rcases family_descends (prefixWord ++ tailWord_146732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146745 : List Nat := [1, 2, 1, 6, 2, 2, 2, 3]
def baseStart_146745 : Nat := 118140960795 + 146745 * 2 ^ 59
def prefixEnd_146745 : Nat := 4983230072969 + 3 ^ 40 * 146745 * 2
def baseEnd_146745 : Nat := 44652277715042129311193

theorem tailTrace_146745 : CollatzResearch.WordTrace tailWord_146745 prefixEnd_146745 44652277715042129311193 := by
  unfold tailWord_146745
  simp only [CollatzResearch.WordTrace]
  refine ⟨5352229853375401895817689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3568153235583601263878459 5352229853375401895817689)
  ·
    refine ⟨4014172390031551421863267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5352229853375401895817689 4014172390031551421863267)
    ·
      refine ⟨6021258585047327132794901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4014172390031551421863267 6021258585047327132794901)
      ·
        refine ⟨282246496174093459349761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6021258585047327132794901 282246496174093459349761)
        ·
          refine ⟨211684872130570094512321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 282246496174093459349761 211684872130570094512321)
          ·
            refine ⟨158763654097927570884241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211684872130570094512321 158763654097927570884241)
            ·
              refine ⟨119072740573445678163181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158763654097927570884241 119072740573445678163181)
              ·
                refine ⟨44652277715042129311193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119072740573445678163181 44652277715042129311193)
                ·
                  rfl

theorem cell19_146745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 3].length) (baseStart_146745 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_146745 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_146745 prefixEnd_146745 := by exact prefixLift 146745
  have htrace : WordTrace (prefixWord ++ tailWord_146745) baseStart_146745 baseEnd_146745 := by
    simpa [prefixWord, tailWord_146745, baseEnd_146745] using wordTrace_append hprefix tailTrace_146745
  have hstable : (prefixWord ++ tailWord_146745).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146745).length < 2 ^ (prefixWord ++ tailWord_146745).sum := by decide
  have hdescent : baseEnd_146745 < baseStart_146745 := by decide
  rcases family_descends (prefixWord ++ tailWord_146745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146781 : List Nat := [1, 4, 5, 1, 1, 1, 2, 4]
def baseStart_146781 : Nat := 118140960795 + 146781 * 2 ^ 59
def prefixEnd_146781 : Nat := 4983230072969 + 3 ^ 40 * 146781 * 2
def baseEnd_146781 : Nat := 44663231969004712511095

theorem tailTrace_146781 : CollatzResearch.WordTrace tailWord_146781 prefixEnd_146781 44663231969004712511095 := by
  unfold tailWord_146781
  simp only [CollatzResearch.WordTrace]
  refine ⟨5353542881244980044128197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3569028587496653362752131 5353542881244980044128197)
  ·
    refine ⟨1003789290233433758274037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5353542881244980044128197 1003789290233433758274037)
    ·
      refine ⟨94105245959384414838191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1003789290233433758274037 94105245959384414838191)
      ·
        refine ⟨141157868939076622257287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94105245959384414838191 141157868939076622257287)
        ·
          refine ⟨211736803408614933385931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141157868939076622257287 211736803408614933385931)
          ·
            refine ⟨317605205112922400078897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211736803408614933385931 317605205112922400078897)
            ·
              refine ⟨238203903834691800059173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 317605205112922400078897 238203903834691800059173)
              ·
                refine ⟨44663231969004712511095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 238203903834691800059173 44663231969004712511095)
                ·
                  rfl

theorem cell19_146781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 4].length) (baseStart_146781 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_146781 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_146781 prefixEnd_146781 := by exact prefixLift 146781
  have htrace : WordTrace (prefixWord ++ tailWord_146781) baseStart_146781 baseEnd_146781 := by
    simpa [prefixWord, tailWord_146781, baseEnd_146781] using wordTrace_append hprefix tailTrace_146781
  have hstable : (prefixWord ++ tailWord_146781).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146781).length < 2 ^ (prefixWord ++ tailWord_146781).sum := by decide
  have hdescent : baseEnd_146781 < baseStart_146781 := by decide
  rcases family_descends (prefixWord ++ tailWord_146781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146787 : List Nat := [1, 1, 1, 5, 2, 3, 2, 4]
def baseStart_146787 : Nat := 118140960795 + 146787 * 2 ^ 59
def prefixEnd_146787 : Nat := 4983230072969 + 3 ^ 40 * 146787 * 2
def baseEnd_146787 : Nat := 44665057677998476377745

theorem tailTrace_146787 : CollatzResearch.WordTrace tailWord_146787 prefixEnd_146787 44665057677998476377745 := by
  unfold tailWord_146787
  simp only [CollatzResearch.WordTrace]
  refine ⟨5353761719223243068846615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3569174479482162045897743 5353761719223243068846615)
  ·
    refine ⟨8030642578834864603269923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5353761719223243068846615 8030642578834864603269923)
    ·
      refine ⟨12045963868252296904904885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8030642578834864603269923 12045963868252296904904885)
      ·
        refine ⟨1129309112648652834834833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12045963868252296904904885 1129309112648652834834833)
        ·
          refine ⟨846981834486489626126125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1129309112648652834834833 846981834486489626126125)
          ·
            refine ⟨317618187932433609797297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 846981834486489626126125 317618187932433609797297)
            ·
              refine ⟨238213640949325207347973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 317618187932433609797297 238213640949325207347973)
              ·
                refine ⟨44665057677998476377745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 238213640949325207347973 44665057677998476377745)
                ·
                  rfl

theorem cell19_146787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 4].length) (baseStart_146787 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_146787 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_146787 prefixEnd_146787 := by exact prefixLift 146787
  have htrace : WordTrace (prefixWord ++ tailWord_146787) baseStart_146787 baseEnd_146787 := by
    simpa [prefixWord, tailWord_146787, baseEnd_146787] using wordTrace_append hprefix tailTrace_146787
  have hstable : (prefixWord ++ tailWord_146787).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146787).length < 2 ^ (prefixWord ++ tailWord_146787).sum := by decide
  have hdescent : baseEnd_146787 < baseStart_146787 := by decide
  rcases family_descends (prefixWord ++ tailWord_146787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146825 : List Nat := [1, 2, 1, 1, 8, 6]
def baseStart_146825 : Nat := 118140960795 + 146825 * 2 ^ 59
def prefixEnd_146825 : Nat := 4983230072969 + 3 ^ 40 * 146825 * 2
def baseEnd_146825 : Nat := 4964068944625071948133

theorem tailTrace_146825 : CollatzResearch.WordTrace tailWord_146825 prefixEnd_146825 4964068944625071948133 := by
  unfold tailWord_146825
  simp only [CollatzResearch.WordTrace]
  refine ⟨5355147693085575558729929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3570098462057050372486619 5355147693085575558729929)
  ·
    refine ⟨4016360769814181669047447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5355147693085575558729929 4016360769814181669047447)
    ·
      refine ⟨6024541154721272503571171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4016360769814181669047447 6024541154721272503571171)
      ·
        refine ⟨9036811732081908755356757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6024541154721272503571171 9036811732081908755356757)
        ·
          refine ⟨105900137485334868226837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 9036811732081908755356757 105900137485334868226837)
          ·
            refine ⟨4964068944625071948133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 105900137485334868226837 4964068944625071948133)
            ·
              rfl

theorem cell19_146825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 6].length) (baseStart_146825 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_146825 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_146825 prefixEnd_146825 := by exact prefixLift 146825
  have htrace : WordTrace (prefixWord ++ tailWord_146825) baseStart_146825 baseEnd_146825 := by
    simpa [prefixWord, tailWord_146825, baseEnd_146825] using wordTrace_append hprefix tailTrace_146825
  have hstable : (prefixWord ++ tailWord_146825).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146825).length < 2 ^ (prefixWord ++ tailWord_146825).sum := by decide
  have hdescent : baseEnd_146825 < baseStart_146825 := by decide
  rcases family_descends (prefixWord ++ tailWord_146825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146840 : List Nat := [2, 1, 2, 5, 3, 1, 1, 4]
def baseStart_146840 : Nat := 118140960795 + 146840 * 2 ^ 59
def prefixEnd_146840 : Nat := 4983230072969 + 3 ^ 40 * 146840 * 2
def baseEnd_146840 : Nat := 44681184774110057199823

theorem tailTrace_146840 : CollatzResearch.WordTrace tailWord_146840 prefixEnd_146840 44681184774110057199823 := by
  unfold tailWord_146840
  simp only [CollatzResearch.WordTrace]
  refine ⟨2677847394015616560262987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3570463192020822080350649 2677847394015616560262987)
  ·
    refine ⟨4016771091023424840394481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2677847394015616560262987 4016771091023424840394481)
    ·
      refine ⟨3012578318267568630295861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4016771091023424840394481 3012578318267568630295861)
      ·
        refine ⟨282429217337584559090237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3012578318267568630295861 282429217337584559090237)
        ·
          refine ⟨105910956501594209658839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 282429217337584559090237 105910956501594209658839)
          ·
            refine ⟨158866434752391314488259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105910956501594209658839 158866434752391314488259)
            ·
              refine ⟨238299652128586971732389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158866434752391314488259 238299652128586971732389)
              ·
                refine ⟨44681184774110057199823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 238299652128586971732389 44681184774110057199823)
                ·
                  rfl

theorem cell19_146840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 4].length) (baseStart_146840 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_146840 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_146840 prefixEnd_146840 := by exact prefixLift 146840
  have htrace : WordTrace (prefixWord ++ tailWord_146840) baseStart_146840 baseEnd_146840 := by
    simpa [prefixWord, tailWord_146840, baseEnd_146840] using wordTrace_append hprefix tailTrace_146840
  have hstable : (prefixWord ++ tailWord_146840).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146840).length < 2 ^ (prefixWord ++ tailWord_146840).sum := by decide
  have hdescent : baseEnd_146840 < baseStart_146840 := by decide
  rcases family_descends (prefixWord ++ tailWord_146840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146941 : List Nat := [1, 4, 1, 1, 1, 4, 7]
def baseStart_146941 : Nat := 118140960795 + 146941 * 2 ^ 59
def prefixEnd_146941 : Nat := 4983230072969 + 3 ^ 40 * 146941 * 2
def baseEnd_146941 : Nat := 14903972514057249651701

theorem tailTrace_146941 : CollatzResearch.WordTrace tailWord_146941 prefixEnd_146941 14903972514057249651701 := by
  unfold tailWord_146941
  simp only [CollatzResearch.WordTrace]
  refine ⟨5359378560665327369952677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3572919040443551579968451 5359378560665327369952677)
  ·
    refine ⟨1004883480124748881866127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5359378560665327369952677 1004883480124748881866127)
    ·
      refine ⟨1507325220187123322799191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1004883480124748881866127 1507325220187123322799191)
      ·
        refine ⟨2260987830280684984198787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1507325220187123322799191 2260987830280684984198787)
        ·
          refine ⟨3391481745421027476298181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2260987830280684984198787 3391481745421027476298181)
          ·
            refine ⟨635902827266442651805909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3391481745421027476298181 635902827266442651805909)
            ·
              refine ⟨14903972514057249651701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 635902827266442651805909 14903972514057249651701)
              ·
                rfl

theorem cell19_146941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 7].length) (baseStart_146941 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_146941 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_146941 prefixEnd_146941 := by exact prefixLift 146941
  have htrace : WordTrace (prefixWord ++ tailWord_146941) baseStart_146941 baseEnd_146941 := by
    simpa [prefixWord, tailWord_146941, baseEnd_146941] using wordTrace_append hprefix tailTrace_146941
  have hstable : (prefixWord ++ tailWord_146941).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146941).length < 2 ^ (prefixWord ++ tailWord_146941).sum := by decide
  have hdescent : baseEnd_146941 < baseStart_146941 := by decide
  rcases family_descends (prefixWord ++ tailWord_146941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147053 : List Nat := [1, 5, 1, 1, 4, 1, 6]
def baseStart_147053 : Nat := 118140960795 + 147053 * 2 ^ 59
def prefixEnd_147053 : Nat := 4983230072969 + 3 ^ 40 * 147053 * 2
def baseEnd_147053 : Nat := 14915332481129558155303

theorem tailTrace_147053 : CollatzResearch.WordTrace tailWord_147053 prefixEnd_147053 14915332481129558155303 := by
  unfold tailWord_147053
  simp only [CollatzResearch.WordTrace]
  refine ⟨5363463536259570498029813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3575642357506380332019875 5363463536259570498029813)
  ·
    refine ⟨502824706524334734190295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5363463536259570498029813 502824706524334734190295)
    ·
      refine ⟨754237059786502101285443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 502824706524334734190295 754237059786502101285443)
      ·
        refine ⟨1131355589679753151928165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 754237059786502101285443 1131355589679753151928165)
        ·
          refine ⟨212129173064953715986531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1131355589679753151928165 212129173064953715986531)
          ·
            refine ⟨318193759597430573979797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212129173064953715986531 318193759597430573979797)
            ·
              refine ⟨14915332481129558155303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 318193759597430573979797 14915332481129558155303)
              ·
                rfl

theorem cell19_147053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 6].length) (baseStart_147053 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_147053 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_147053 prefixEnd_147053 := by exact prefixLift 147053
  have htrace : WordTrace (prefixWord ++ tailWord_147053) baseStart_147053 baseEnd_147053 := by
    simpa [prefixWord, tailWord_147053, baseEnd_147053] using wordTrace_append hprefix tailTrace_147053
  have hstable : (prefixWord ++ tailWord_147053).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147053).length < 2 ^ (prefixWord ++ tailWord_147053).sum := by decide
  have hdescent : baseEnd_147053 < baseStart_147053 := by decide
  rcases family_descends (prefixWord ++ tailWord_147053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147106 : List Nat := [3, 3, 1, 4, 2, 1, 5]
def baseStart_147106 : Nat := 118140960795 + 147106 * 2 ^ 59
def prefixEnd_147106 : Nat := 4983230072969 + 3 ^ 40 * 147106 * 2
def baseEnd_147106 : Nat := 14920708179833418429329

theorem tailTrace_147106 : CollatzResearch.WordTrace tailWord_147106 prefixEnd_147106 14920708179833418429329 := by
  unfold tailWord_147106
  simp only [CollatzResearch.WordTrace]
  refine ⟨1341349151266890137427293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3576931070045040366472781 1341349151266890137427293)
  ·
    refine ⟨503005931725083801535235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1341349151266890137427293 503005931725083801535235)
    ·
      refine ⟨754508897587625702302853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 503005931725083801535235 754508897587625702302853)
      ·
        refine ⟨141470418297679819181785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 754508897587625702302853 141470418297679819181785)
        ·
          refine ⟨106102813723259864386339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141470418297679819181785 106102813723259864386339)
          ·
            refine ⟨159154220584889796579509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106102813723259864386339 159154220584889796579509)
            ·
              refine ⟨14920708179833418429329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 159154220584889796579509 14920708179833418429329)
              ·
                rfl

theorem cell19_147106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 5].length) (baseStart_147106 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_147106 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_147106 prefixEnd_147106 := by exact prefixLift 147106
  have htrace : WordTrace (prefixWord ++ tailWord_147106) baseStart_147106 baseEnd_147106 := by
    simpa [prefixWord, tailWord_147106, baseEnd_147106] using wordTrace_append hprefix tailTrace_147106
  have hstable : (prefixWord ++ tailWord_147106).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147106).length < 2 ^ (prefixWord ++ tailWord_147106).sum := by decide
  have hdescent : baseEnd_147106 < baseStart_147106 := by decide
  rcases family_descends (prefixWord ++ tailWord_147106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147150 : List Nat := [4, 1, 1, 1, 3, 1, 1, 7]
def baseStart_147150 : Nat := 118140960795 + 147150 * 2 ^ 59
def prefixEnd_147150 : Nat := 4983230072969 + 3 ^ 40 * 147150 * 2
def baseEnd_147150 : Nat := 44775513072121190310089

theorem tailTrace_147150 : CollatzResearch.WordTrace tailWord_147150 prefixEnd_147150 44775513072121190310089 := by
  unfold tailWord_147150
  simp only [CollatzResearch.WordTrace]
  refine ⟨670875177113519508038863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3578000944605437376207269 670875177113519508038863)
  ·
    refine ⟨1006312765670279262058295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 670875177113519508038863 1006312765670279262058295)
    ·
      refine ⟨1509469148505418893087443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1006312765670279262058295 1509469148505418893087443)
      ·
        refine ⟨2264203722758128339631165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1509469148505418893087443 2264203722758128339631165)
        ·
          refine ⟨849076396034298127361687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2264203722758128339631165 849076396034298127361687)
          ·
            refine ⟨1273614594051447191042531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 849076396034298127361687 1273614594051447191042531)
            ·
              refine ⟨1910421891077170786563797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1273614594051447191042531 1910421891077170786563797)
              ·
                refine ⟨44775513072121190310089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1910421891077170786563797 44775513072121190310089)
                ·
                  rfl

theorem cell19_147150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_147150 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_147150 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_147150 prefixEnd_147150 := by exact prefixLift 147150
  have htrace : WordTrace (prefixWord ++ tailWord_147150) baseStart_147150 baseEnd_147150 := by
    simpa [prefixWord, tailWord_147150, baseEnd_147150] using wordTrace_append hprefix tailTrace_147150
  have hstable : (prefixWord ++ tailWord_147150).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147150).length < 2 ^ (prefixWord ++ tailWord_147150).sum := by decide
  have hdescent : baseEnd_147150 < baseStart_147150 := by decide
  rcases family_descends (prefixWord ++ tailWord_147150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147165 : List Nat := [1, 4, 3, 3, 2, 6]
def baseStart_147165 : Nat := 118140960795 + 147165 * 2 ^ 59
def prefixEnd_147165 : Nat := 4983230072969 + 3 ^ 40 * 147165 * 2
def baseEnd_147165 : Nat := 4975564149400622219635

theorem tailTrace_147165 : CollatzResearch.WordTrace tailWord_147165 prefixEnd_147165 4975564149400622219635 := by
  unfold tailWord_147165
  simp only [CollatzResearch.WordTrace]
  refine ⟨5367548511853813626106949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3578365674569209084071299 5367548511853813626106949)
  ·
    refine ⟨1006415345972590054895053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5367548511853813626106949 1006415345972590054895053)
    ·
      refine ⟨377405754739721270585645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1006415345972590054895053 377405754739721270585645)
      ·
        refine ⟨141527158027395476469617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 377405754739721270585645 141527158027395476469617)
        ·
          refine ⟨106145368520546607352213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141527158027395476469617 106145368520546607352213)
          ·
            refine ⟨4975564149400622219635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 106145368520546607352213 4975564149400622219635)
            ·
              rfl

theorem cell19_147165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 6].length) (baseStart_147165 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_147165 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_147165 prefixEnd_147165 := by exact prefixLift 147165
  have htrace : WordTrace (prefixWord ++ tailWord_147165) baseStart_147165 baseEnd_147165 := by
    simpa [prefixWord, tailWord_147165, baseEnd_147165] using wordTrace_append hprefix tailTrace_147165
  have hstable : (prefixWord ++ tailWord_147165).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147165).length < 2 ^ (prefixWord ++ tailWord_147165).sum := by decide
  have hdescent : baseEnd_147165 < baseStart_147165 := by decide
  rcases family_descends (prefixWord ++ tailWord_147165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147169 : List Nat := [1, 2, 3, 1, 5, 7]
def baseStart_147169 : Nat := 118140960795 + 147169 * 2 ^ 59
def prefixEnd_147169 : Nat := 4983230072969 + 3 ^ 40 * 147169 * 2
def baseEnd_147169 : Nat := 4975699387103863987535

theorem tailTrace_147169 : CollatzResearch.WordTrace tailWord_147169 prefixEnd_147169 4975699387103863987535 := by
  unfold tailWord_147169
  simp only [CollatzResearch.WordTrace]
  refine ⟨5367694403839322309252561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3578462935892881539501707 5367694403839322309252561)
  ·
    refine ⟨4025770802879491731939421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5367694403839322309252561 4025770802879491731939421)
    ·
      refine ⟨1509664051079809399477283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4025770802879491731939421 1509664051079809399477283)
      ·
        refine ⟨2264496076619714099215925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1509664051079809399477283 2264496076619714099215925)
        ·
          refine ⟨212296507183098196801493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2264496076619714099215925 212296507183098196801493)
          ·
            refine ⟨4975699387103863987535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 212296507183098196801493 4975699387103863987535)
            ·
              rfl

theorem cell19_147169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 7].length) (baseStart_147169 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_147169 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_147169 prefixEnd_147169 := by exact prefixLift 147169
  have htrace : WordTrace (prefixWord ++ tailWord_147169) baseStart_147169 baseEnd_147169 := by
    simpa [prefixWord, tailWord_147169, baseEnd_147169] using wordTrace_append hprefix tailTrace_147169
  have hstable : (prefixWord ++ tailWord_147169).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147169).length < 2 ^ (prefixWord ++ tailWord_147169).sum := by decide
  have hdescent : baseEnd_147169 < baseStart_147169 := by decide
  rcases family_descends (prefixWord ++ tailWord_147169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147220 : List Nat := [2, 4, 4, 1, 1, 1, 6]
def baseStart_147220 : Nat := 118140960795 + 147220 * 2 ^ 59
def prefixEnd_147220 : Nat := 4983230072969 + 3 ^ 40 * 147220 * 2
def baseEnd_147220 : Nat := 14932271003460589584781

theorem tailTrace_147220 : CollatzResearch.WordTrace tailWord_147220 prefixEnd_147220 14932271003460589584781 := by
  unfold tailWord_147220
  simp only [CollatzResearch.WordTrace]
  refine ⟨2684777263327279009679557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3579703017769705346239409 2684777263327279009679557)
  ·
    refine ⟨503395736873864814314917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2684777263327279009679557 503395736873864814314917)
    ·
      refine ⟨94386700663849652684047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 503395736873864814314917 94386700663849652684047)
      ·
        refine ⟨141580050995774479026071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94386700663849652684047 141580050995774479026071)
        ·
          refine ⟨212370076493661718539107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141580050995774479026071 212370076493661718539107)
          ·
            refine ⟨318555114740492577808661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212370076493661718539107 318555114740492577808661)
            ·
              refine ⟨14932271003460589584781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 318555114740492577808661 14932271003460589584781)
              ·
                rfl

theorem cell19_147220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 6].length) (baseStart_147220 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_147220 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_147220 prefixEnd_147220 := by exact prefixLift 147220
  have htrace : WordTrace (prefixWord ++ tailWord_147220) baseStart_147220 baseEnd_147220 := by
    simpa [prefixWord, tailWord_147220, baseEnd_147220] using wordTrace_append hprefix tailTrace_147220
  have hstable : (prefixWord ++ tailWord_147220).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147220).length < 2 ^ (prefixWord ++ tailWord_147220).sum := by decide
  have hdescent : baseEnd_147220 < baseStart_147220 := by decide
  rcases family_descends (prefixWord ++ tailWord_147220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147226 : List Nat := [3, 1, 1, 3, 2, 3, 6]
def baseStart_147226 : Nat := 118140960795 + 147226 * 2 ^ 59
def prefixEnd_147226 : Nat := 4983230072969 + 3 ^ 40 * 147226 * 2
def baseEnd_147226 : Nat := 14932879573125177540331

theorem tailTrace_147226 : CollatzResearch.WordTrace tailWord_147226 prefixEnd_147226 14932879573125177540331 := by
  unfold tailWord_147226
  simp only [CollatzResearch.WordTrace]
  refine ⟨1342443341158205261019383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3579848909755214029385021 1342443341158205261019383)
  ·
    refine ⟨2013665011737307891529075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1342443341158205261019383 2013665011737307891529075)
    ·
      refine ⟨3020497517605961837293613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2013665011737307891529075 3020497517605961837293613)
      ·
        refine ⟨1132686569102235688985105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3020497517605961837293613 1132686569102235688985105)
        ·
          refine ⟨849514926826676766738829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1132686569102235688985105 849514926826676766738829)
          ·
            refine ⟨318568097560003787527061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 849514926826676766738829 318568097560003787527061)
            ·
              refine ⟨14932879573125177540331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 318568097560003787527061 14932879573125177540331)
              ·
                rfl

theorem cell19_147226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 6].length) (baseStart_147226 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_147226 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_147226 prefixEnd_147226 := by exact prefixLift 147226
  have htrace : WordTrace (prefixWord ++ tailWord_147226) baseStart_147226 baseEnd_147226 := by
    simpa [prefixWord, tailWord_147226, baseEnd_147226] using wordTrace_append hprefix tailTrace_147226
  have hstable : (prefixWord ++ tailWord_147226).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147226).length < 2 ^ (prefixWord ++ tailWord_147226).sum := by decide
  have hdescent : baseEnd_147226 < baseStart_147226 := by decide
  rcases family_descends (prefixWord ++ tailWord_147226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147262 : List Nat := [4, 2, 1, 2, 2, 2, 1, 5]
def baseStart_147262 : Nat := 118140960795 + 147262 * 2 ^ 59
def prefixEnd_147262 : Nat := 4983230072969 + 3 ^ 40 * 147262 * 2
def baseEnd_147262 : Nat := 44809592973338115820895

theorem tailTrace_147262 : CollatzResearch.WordTrace tailWord_147262 prefixEnd_147262 44809592973338115820895 := by
  unfold tailWord_147262
  simp only [CollatzResearch.WordTrace]
  refine ⟨671385799062799899048505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3580724261668266128258693 671385799062799899048505)
  ·
    refine ⟨503539349297099924286379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 671385799062799899048505 503539349297099924286379)
    ·
      refine ⟨755309023945649886429569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 503539349297099924286379 755309023945649886429569)
      ·
        refine ⟨566481767959237414822177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 755309023945649886429569 566481767959237414822177)
        ·
          refine ⟨424861325969428061116633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 566481767959237414822177 424861325969428061116633)
          ·
            refine ⟨318645994477071045837475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 424861325969428061116633 318645994477071045837475)
            ·
              refine ⟨477968991715606568756213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 318645994477071045837475 477968991715606568756213)
              ·
                refine ⟨44809592973338115820895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 477968991715606568756213 44809592973338115820895)
                ·
                  rfl

theorem cell19_147262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_147262 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_147262 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_147262 prefixEnd_147262 := by exact prefixLift 147262
  have htrace : WordTrace (prefixWord ++ tailWord_147262) baseStart_147262 baseEnd_147262 := by
    simpa [prefixWord, tailWord_147262, baseEnd_147262] using wordTrace_append hprefix tailTrace_147262
  have hstable : (prefixWord ++ tailWord_147262).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147262).length < 2 ^ (prefixWord ++ tailWord_147262).sum := by decide
  have hdescent : baseEnd_147262 < baseStart_147262 := by decide
  rcases family_descends (prefixWord ++ tailWord_147262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147300 : List Nat := [2, 3, 1, 1, 5, 1, 2, 4]
def baseStart_147300 : Nat := 118140960795 + 147300 * 2 ^ 59
def prefixEnd_147300 : Nat := 4983230072969 + 3 ^ 40 * 147300 * 2
def baseEnd_147300 : Nat := 44821155796965286976347

theorem tailTrace_147300 : CollatzResearch.WordTrace tailWord_147300 prefixEnd_147300 44821155796965286976347 := by
  unfold tailWord_147300
  simp only [CollatzResearch.WordTrace]
  refine ⟨2686236183182365841135677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3581648244243154454847569 2686236183182365841135677)
  ·
    refine ⟨1007338568693387190425879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2686236183182365841135677 1007338568693387190425879)
    ·
      refine ⟨1511007853040080785638819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1007338568693387190425879 1511007853040080785638819)
      ·
        refine ⟨2266511779560121178458229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1511007853040080785638819 2266511779560121178458229)
        ·
          refine ⟨212485479333761360480459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2266511779560121178458229 212485479333761360480459)
          ·
            refine ⟨318728219000642040720689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212485479333761360480459 318728219000642040720689)
            ·
              refine ⟨239046164250481530540517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 318728219000642040720689 239046164250481530540517)
              ·
                refine ⟨44821155796965286976347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 239046164250481530540517 44821155796965286976347)
                ·
                  rfl

theorem cell19_147300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 4].length) (baseStart_147300 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_147300 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_147300 prefixEnd_147300 := by exact prefixLift 147300
  have htrace : WordTrace (prefixWord ++ tailWord_147300) baseStart_147300 baseEnd_147300 := by
    simpa [prefixWord, tailWord_147300, baseEnd_147300] using wordTrace_append hprefix tailTrace_147300
  have hstable : (prefixWord ++ tailWord_147300).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147300).length < 2 ^ (prefixWord ++ tailWord_147300).sum := by decide
  have hdescent : baseEnd_147300 < baseStart_147300 := by decide
  rcases family_descends (prefixWord ++ tailWord_147300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147338 : List Nat := [3, 1, 2, 4, 3, 6]
def baseStart_147338 : Nat := 118140960795 + 147338 * 2 ^ 59
def prefixEnd_147338 : Nat := 4983230072969 + 3 ^ 40 * 147338 * 2
def baseEnd_147338 : Nat := 4981413180065828681311

theorem tailTrace_147338 : CollatzResearch.WordTrace tailWord_147338 prefixEnd_147338 4981413180065828681311 := by
  unfold tailWord_147338
  simp only [CollatzResearch.WordTrace]
  refine ⟨1343464585056766043038667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3582572226818042781436445 1343464585056766043038667)
  ·
    refine ⟨2015196877585149064558001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1343464585056766043038667 2015196877585149064558001)
    ·
      refine ⟨1511397658188861798418501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2015196877585149064558001 1511397658188861798418501)
      ·
        refine ⟨283387060910411587203469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1511397658188861798418501 283387060910411587203469)
        ·
          refine ⟨106270147841404345201301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 283387060910411587203469 106270147841404345201301)
          ·
            refine ⟨4981413180065828681311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 106270147841404345201301 4981413180065828681311)
            ·
              rfl

theorem cell19_147338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 6].length) (baseStart_147338 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_147338 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_147338 prefixEnd_147338 := by exact prefixLift 147338
  have htrace : WordTrace (prefixWord ++ tailWord_147338) baseStart_147338 baseEnd_147338 := by
    simpa [prefixWord, tailWord_147338, baseEnd_147338] using wordTrace_append hprefix tailTrace_147338
  have hstable : (prefixWord ++ tailWord_147338).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147338).length < 2 ^ (prefixWord ++ tailWord_147338).sum := by decide
  have hdescent : baseEnd_147338 < baseStart_147338 := by decide
  rcases family_descends (prefixWord ++ tailWord_147338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147357 : List Nat := [1, 4, 2, 1, 2, 4, 1, 4]
def baseStart_147357 : Nat := 118140960795 + 147357 * 2 ^ 59
def prefixEnd_147357 : Nat := 4983230072969 + 3 ^ 40 * 147357 * 2
def baseEnd_147357 : Nat := 44838500032406043709525

theorem tailTrace_147357 : CollatzResearch.WordTrace tailWord_147357 prefixEnd_147357 44838500032406043709525 := by
  unfold tailWord_147357
  simp only [CollatzResearch.WordTrace]
  refine ⟨5374551327158230417096325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3583034218105486944730883 5374551327158230417096325)
  ·
    refine ⟨1007728373842168203205561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5374551327158230417096325 1007728373842168203205561)
    ·
      refine ⟨755796280381626152404171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1007728373842168203205561 755796280381626152404171)
      ·
        refine ⟨1133694420572439228606257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 755796280381626152404171 1133694420572439228606257)
        ·
          refine ⟨850270815429329421454693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1133694420572439228606257 850270815429329421454693)
          ·
            refine ⟨159425777892999266522755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 850270815429329421454693 159425777892999266522755)
            ·
              refine ⟨239138666839498899784133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159425777892999266522755 239138666839498899784133)
              ·
                refine ⟨44838500032406043709525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 239138666839498899784133 44838500032406043709525)
                ·
                  rfl

theorem cell19_147357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 4].length) (baseStart_147357 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_147357 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_147357 prefixEnd_147357 := by exact prefixLift 147357
  have htrace : WordTrace (prefixWord ++ tailWord_147357) baseStart_147357 baseEnd_147357 := by
    simpa [prefixWord, tailWord_147357, baseEnd_147357] using wordTrace_append hprefix tailTrace_147357
  have hstable : (prefixWord ++ tailWord_147357).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147357).length < 2 ^ (prefixWord ++ tailWord_147357).sum := by decide
  have hdescent : baseEnd_147357 < baseStart_147357 := by decide
  rcases family_descends (prefixWord ++ tailWord_147357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147431 : List Nat := [1, 1, 5, 2, 3, 2, 2, 3]
def baseStart_147431 : Nat := 118140960795 + 147431 * 2 ^ 59
def prefixEnd_147431 : Nat := 4983230072969 + 3 ^ 40 * 147431 * 2
def baseEnd_147431 : Nat := 44861017109995798064879

theorem tailTrace_147431 : CollatzResearch.WordTrace tailWord_147431 prefixEnd_147431 44861017109995798064879 := by
  unfold tailWord_147431
  simp only [CollatzResearch.WordTrace]
  refine ⟨5377250328890141055290147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3584833552593427370193431 5377250328890141055290147)
  ·
    refine ⟨8065875493335211582935221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5377250328890141055290147 8065875493335211582935221)
    ·
      refine ⟨756175827500176085900177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8065875493335211582935221 756175827500176085900177)
      ·
        refine ⟨567131870625132064425133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 756175827500176085900177 567131870625132064425133)
        ·
          refine ⟨212674451484424524159425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 567131870625132064425133 212674451484424524159425)
          ·
            refine ⟨159505838613318393119569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212674451484424524159425 159505838613318393119569)
            ·
              refine ⟨119629378959988794839677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159505838613318393119569 119629378959988794839677)
              ·
                refine ⟨44861017109995798064879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119629378959988794839677 44861017109995798064879)
                ·
                  rfl

theorem cell19_147431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 3].length) (baseStart_147431 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_147431 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_147431 prefixEnd_147431 := by exact prefixLift 147431
  have htrace : WordTrace (prefixWord ++ tailWord_147431) baseStart_147431 baseEnd_147431 := by
    simpa [prefixWord, tailWord_147431, baseEnd_147431] using wordTrace_append hprefix tailTrace_147431
  have hstable : (prefixWord ++ tailWord_147431).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147431).length < 2 ^ (prefixWord ++ tailWord_147431).sum := by decide
  have hdescent : baseEnd_147431 < baseStart_147431 := by decide
  rcases family_descends (prefixWord ++ tailWord_147431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147475 : List Nat := [1, 1, 1, 2, 1, 4, 3, 6]
def baseStart_147475 : Nat := 118140960795 + 147475 * 2 ^ 59
def prefixEnd_147475 : Nat := 4983230072969 + 3 ^ 40 * 147475 * 2
def baseEnd_147475 : Nat := 44874405642616733086981

theorem tailTrace_147475 : CollatzResearch.WordTrace tailWord_147475 prefixEnd_147475 44874405642616733086981 := by
  unfold tailWord_147475
  simp only [CollatzResearch.WordTrace]
  refine ⟨5378855140730736569891879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3585903427153824379927919 5378855140730736569891879)
  ·
    refine ⟨8068282711096104854837819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5378855140730736569891879 8068282711096104854837819)
    ·
      refine ⟨12102424066644157282256729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8068282711096104854837819 12102424066644157282256729)
      ·
        refine ⟨9076818049983117961692547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12102424066644157282256729 9076818049983117961692547)
        ·
          refine ⟨13615227074974676942538821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9076818049983117961692547 13615227074974676942538821)
          ·
            refine ⟨2552855076557751926726029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13615227074974676942538821 2552855076557751926726029)
            ·
              refine ⟨957320653709156972522261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2552855076557751926726029 957320653709156972522261)
              ·
                refine ⟨44874405642616733086981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 957320653709156972522261 44874405642616733086981)
                ·
                  rfl

theorem cell19_147475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 6].length) (baseStart_147475 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_147475 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_147475 prefixEnd_147475 := by exact prefixLift 147475
  have htrace : WordTrace (prefixWord ++ tailWord_147475) baseStart_147475 baseEnd_147475 := by
    simpa [prefixWord, tailWord_147475, baseEnd_147475] using wordTrace_append hprefix tailTrace_147475
  have hstable : (prefixWord ++ tailWord_147475).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147475).length < 2 ^ (prefixWord ++ tailWord_147475).sum := by decide
  have hdescent : baseEnd_147475 < baseStart_147475 := by decide
  rcases family_descends (prefixWord ++ tailWord_147475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147513 : List Nat := [1, 2, 1, 5, 10]
def baseStart_147513 : Nat := 118140960795 + 147513 * 2 ^ 59
def prefixEnd_147513 : Nat := 4983230072969 + 3 ^ 40 * 147513 * 2
def baseEnd_147513 : Nat := 1662443276527552008979

theorem tailTrace_147513 : CollatzResearch.WordTrace tailWord_147513 prefixEnd_147513 1662443276527552008979 := by
  unfold tailWord_147513
  simp only [CollatzResearch.WordTrace]
  refine ⟨5380241114593069059775193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3586827409728712706516795 5380241114593069059775193)
  ·
    refine ⟨4035180835944801794831395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5380241114593069059775193 4035180835944801794831395)
    ·
      refine ⟨6052771253917202692247093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4035180835944801794831395 6052771253917202692247093)
      ·
        refine ⟨567447305054737752398165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6052771253917202692247093 567447305054737752398165)
        ·
          refine ⟨1662443276527552008979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 567447305054737752398165 1662443276527552008979)
          ·
            rfl

theorem cell19_147513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 10].length) (baseStart_147513 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_147513 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_147513 prefixEnd_147513 := by exact prefixLift 147513
  have htrace : WordTrace (prefixWord ++ tailWord_147513) baseStart_147513 baseEnd_147513 := by
    simpa [prefixWord, tailWord_147513, baseEnd_147513] using wordTrace_append hprefix tailTrace_147513
  have hstable : (prefixWord ++ tailWord_147513).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147513).length < 2 ^ (prefixWord ++ tailWord_147513).sum := by decide
  have hdescent : baseEnd_147513 < baseStart_147513 := by decide
  rcases family_descends (prefixWord ++ tailWord_147513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147623 : List Nat := [1, 1, 6, 2, 2, 2, 5]
def baseStart_147623 : Nat := 118140960795 + 147623 * 2 ^ 59
def prefixEnd_147623 : Nat := 4983230072969 + 3 ^ 40 * 147623 * 2
def baseEnd_147623 : Nat := 14973146599265413932563

theorem tailTrace_147623 : CollatzResearch.WordTrace tailWord_147623 prefixEnd_147623 14973146599265413932563 := by
  unfold tailWord_147623
  simp only [CollatzResearch.WordTrace]
  refine ⟨5384253144194557846279523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3589502096129705230853015 5384253144194557846279523)
  ·
    refine ⟨8076379716291836769419285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5384253144194557846279523 8076379716291836769419285)
    ·
      refine ⟨378580299201179848566529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8076379716291836769419285 378580299201179848566529)
      ·
        refine ⟨283935224400884886424897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 378580299201179848566529 283935224400884886424897)
        ·
          refine ⟨212951418300663664818673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283935224400884886424897 212951418300663664818673)
          ·
            refine ⟨159713563725497748614005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212951418300663664818673 159713563725497748614005)
            ·
              refine ⟨14973146599265413932563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 159713563725497748614005 14973146599265413932563)
              ·
                rfl

theorem cell19_147623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 5].length) (baseStart_147623 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_147623 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_147623 prefixEnd_147623 := by exact prefixLift 147623
  have htrace : WordTrace (prefixWord ++ tailWord_147623) baseStart_147623 baseEnd_147623 := by
    simpa [prefixWord, tailWord_147623, baseEnd_147623] using wordTrace_append hprefix tailTrace_147623
  have hstable : (prefixWord ++ tailWord_147623).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147623).length < 2 ^ (prefixWord ++ tailWord_147623).sum := by decide
  have hdescent : baseEnd_147623 < baseStart_147623 := by decide
  rcases family_descends (prefixWord ++ tailWord_147623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147665 : List Nat := [1, 2, 2, 1, 2, 2, 4, 5]
def baseStart_147665 : Nat := 118140960795 + 147665 * 2 ^ 59
def prefixEnd_147665 : Nat := 4983230072969 + 3 ^ 40 * 147665 * 2
def baseEnd_147665 : Nat := 44932219760752588864241

theorem tailTrace_147665 : CollatzResearch.WordTrace tailWord_147665 prefixEnd_147665 44932219760752588864241 := by
  unfold tailWord_147665
  simp only [CollatzResearch.WordTrace]
  refine ⟨5385785010042399019308449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3590523340028266012872299 5385785010042399019308449)
  ·
    refine ⟨4039338757531799264481337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5385785010042399019308449 4039338757531799264481337)
    ·
      refine ⟨3029504068148849448361003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4039338757531799264481337 3029504068148849448361003)
      ·
        refine ⟨4544256102223274172541505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3029504068148849448361003 4544256102223274172541505)
        ·
          refine ⟨3408192076667455629406129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4544256102223274172541505 3408192076667455629406129)
          ·
            refine ⟨2556144057500591722054597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3408192076667455629406129 2556144057500591722054597)
            ·
              refine ⟨479277010781360947885237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2556144057500591722054597 479277010781360947885237)
              ·
                refine ⟨44932219760752588864241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 479277010781360947885237 44932219760752588864241)
                ·
                  rfl

theorem cell19_147665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 5].length) (baseStart_147665 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_147665 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_147665 prefixEnd_147665 := by exact prefixLift 147665
  have htrace : WordTrace (prefixWord ++ tailWord_147665) baseStart_147665 baseEnd_147665 := by
    simpa [prefixWord, tailWord_147665, baseEnd_147665] using wordTrace_append hprefix tailTrace_147665
  have hstable : (prefixWord ++ tailWord_147665).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147665).length < 2 ^ (prefixWord ++ tailWord_147665).sum := by decide
  have hdescent : baseEnd_147665 < baseStart_147665 := by decide
  rcases family_descends (prefixWord ++ tailWord_147665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147722 : List Nat := [3, 1, 2, 2, 1, 1, 2, 7]
def baseStart_147722 : Nat := 118140960795 + 147722 * 2 ^ 59
def prefixEnd_147722 : Nat := 4983230072969 + 3 ^ 40 * 147722 * 2
def baseEnd_147722 : Nat := 44949563996193345597419

theorem tailTrace_147722 : CollatzResearch.WordTrace tailWord_147722 prefixEnd_147722 44949563996193345597419 := by
  unfold tailWord_147722
  simp only [CollatzResearch.WordTrace]
  refine ⟨1346965992708974438533355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3591909313890598502755613 1346965992708974438533355)
  ·
    refine ⟨2020448989063461657800033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1346965992708974438533355 2020448989063461657800033)
    ·
      refine ⟨1515336741797596243350025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2020448989063461657800033 1515336741797596243350025)
      ·
        refine ⟨1136502556348197182512519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1515336741797596243350025 1136502556348197182512519)
        ·
          refine ⟨1704753834522295773768779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1136502556348197182512519 1704753834522295773768779)
          ·
            refine ⟨2557130751783443660653169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1704753834522295773768779 2557130751783443660653169)
            ·
              refine ⟨1917848063837582745489877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2557130751783443660653169 1917848063837582745489877)
              ·
                refine ⟨44949563996193345597419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1917848063837582745489877 44949563996193345597419)
                ·
                  rfl

theorem cell19_147722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_147722 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_147722 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_147722 prefixEnd_147722 := by exact prefixLift 147722
  have htrace : WordTrace (prefixWord ++ tailWord_147722) baseStart_147722 baseEnd_147722 := by
    simpa [prefixWord, tailWord_147722, baseEnd_147722] using wordTrace_append hprefix tailTrace_147722
  have hstable : (prefixWord ++ tailWord_147722).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147722).length < 2 ^ (prefixWord ++ tailWord_147722).sum := by decide
  have hdescent : baseEnd_147722 < baseStart_147722 := by decide
  rcases family_descends (prefixWord ++ tailWord_147722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147796 : List Nat := [2, 4, 1, 1, 2, 4, 5]
def baseStart_147796 : Nat := 118140960795 + 147796 * 2 ^ 59
def prefixEnd_147796 : Nat := 4983230072969 + 3 ^ 40 * 147796 * 2
def baseEnd_147796 : Nat := 14990693691261033317591

theorem tailTrace_147796 : CollatzResearch.WordTrace tailWord_147796 prefixEnd_147796 14990693691261033317591 := by
  unfold tailWord_147796
  simp only [CollatzResearch.WordTrace]
  refine ⟨2695281486283904196163621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3593708648378538928218161 2695281486283904196163621)
  ·
    refine ⟨505365278678232036780679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2695281486283904196163621 505365278678232036780679)
    ·
      refine ⟨758047918017348055171019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 505365278678232036780679 758047918017348055171019)
      ·
        refine ⟨1137071877026022082756529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 758047918017348055171019 1137071877026022082756529)
        ·
          refine ⟨852803907769516562067397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1137071877026022082756529 852803907769516562067397)
          ·
            refine ⟨159900732706784355387637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 852803907769516562067397 159900732706784355387637)
            ·
              refine ⟨14990693691261033317591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 159900732706784355387637 14990693691261033317591)
              ·
                rfl

theorem cell19_147796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 5].length) (baseStart_147796 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_147796 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_147796 prefixEnd_147796 := by exact prefixLift 147796
  have htrace : WordTrace (prefixWord ++ tailWord_147796) baseStart_147796 baseEnd_147796 := by
    simpa [prefixWord, tailWord_147796, baseEnd_147796] using wordTrace_append hprefix tailTrace_147796
  have hstable : (prefixWord ++ tailWord_147796).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147796).length < 2 ^ (prefixWord ++ tailWord_147796).sum := by decide
  have hdescent : baseEnd_147796 < baseStart_147796 := by decide
  rcases family_descends (prefixWord ++ tailWord_147796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147815 : List Nat := [1, 1, 5, 1, 3, 2, 2, 4]
def baseStart_147815 : Nat := 118140960795 + 147815 * 2 ^ 59
def prefixEnd_147815 : Nat := 4983230072969 + 3 ^ 40 * 147815 * 2
def baseEnd_147815 : Nat := 44977862485596685530499

theorem tailTrace_147815 : CollatzResearch.WordTrace tailWord_147815 prefixEnd_147815 44977862485596685530499 := by
  unfold tailWord_147815
  simp only [CollatzResearch.WordTrace]
  refine ⟨5391255959498974637268899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3594170639665983091512599 5391255959498974637268899)
  ·
    refine ⟨8086883939248461955903349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5391255959498974637268899 8086883939248461955903349)
    ·
      refine ⟨758145369304543308365939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8086883939248461955903349 758145369304543308365939)
      ·
        refine ⟨1137218053956814962548909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 758145369304543308365939 1137218053956814962548909)
        ·
          refine ⟨426456770233805610955841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1137218053956814962548909 426456770233805610955841)
          ·
            refine ⟨319842577675354208216881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 426456770233805610955841 319842577675354208216881)
            ·
              refine ⟨239881933256515656162661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 319842577675354208216881 239881933256515656162661)
              ·
                refine ⟨44977862485596685530499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 239881933256515656162661 44977862485596685530499)
                ·
                  rfl

theorem cell19_147815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 4].length) (baseStart_147815 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_147815 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_147815 prefixEnd_147815 := by exact prefixLift 147815
  have htrace : WordTrace (prefixWord ++ tailWord_147815) baseStart_147815 baseEnd_147815 := by
    simpa [prefixWord, tailWord_147815, baseEnd_147815] using wordTrace_append hprefix tailTrace_147815
  have hstable : (prefixWord ++ tailWord_147815).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147815).length < 2 ^ (prefixWord ++ tailWord_147815).sum := by decide
  have hdescent : baseEnd_147815 < baseStart_147815 := by decide
  rcases family_descends (prefixWord ++ tailWord_147815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147817 : List Nat := [1, 2, 1, 1, 1, 3, 6, 4]
def baseStart_147817 : Nat := 118140960795 + 147817 * 2 ^ 59
def prefixEnd_147817 : Nat := 4983230072969 + 3 ^ 40 * 147817 * 2
def baseEnd_147817 : Nat := 44978471055261273486049

theorem tailTrace_147817 : CollatzResearch.WordTrace tailWord_147817 prefixEnd_147817 44978471055261273486049 := by
  unfold tailWord_147817
  simp only [CollatzResearch.WordTrace]
  refine ⟨5391328905491728978841705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3594219270327819319227803 5391328905491728978841705)
  ·
    refine ⟨4043496679118796734131279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5391328905491728978841705 4043496679118796734131279)
    ·
      refine ⟨6065245018678195101196919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4043496679118796734131279 6065245018678195101196919)
      ·
        refine ⟨9097867528017292651795379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6065245018678195101196919 9097867528017292651795379)
        ·
          refine ⟨13646801292025938977693069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9097867528017292651795379 13646801292025938977693069)
          ·
            refine ⟨5117550484509727116634901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13646801292025938977693069 5117550484509727116634901)
            ·
              refine ⟨239885178961393458592261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5117550484509727116634901 239885178961393458592261)
              ·
                refine ⟨44978471055261273486049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 239885178961393458592261 44978471055261273486049)
                ·
                  rfl

theorem cell19_147817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 4].length) (baseStart_147817 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_147817 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_147817 prefixEnd_147817 := by exact prefixLift 147817
  have htrace : WordTrace (prefixWord ++ tailWord_147817) baseStart_147817 baseEnd_147817 := by
    simpa [prefixWord, tailWord_147817, baseEnd_147817] using wordTrace_append hprefix tailTrace_147817
  have hstable : (prefixWord ++ tailWord_147817).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147817).length < 2 ^ (prefixWord ++ tailWord_147817).sum := by decide
  have hdescent : baseEnd_147817 < baseStart_147817 := by decide
  rcases family_descends (prefixWord ++ tailWord_147817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147870 : List Nat := [4, 3, 1, 2, 1, 1, 3, 4]
def baseStart_147870 : Nat := 118140960795 + 147870 * 2 ^ 59
def prefixEnd_147870 : Nat := 4983230072969 + 3 ^ 40 * 147870 * 2
def baseEnd_147870 : Nat := 44994598151372854308127

theorem tailTrace_147870 : CollatzResearch.WordTrace tailWord_147870 prefixEnd_147870 44994598151372854308127 := by
  unfold tailWord_147870
  simp only [CollatzResearch.WordTrace]
  refine ⟨674157746787464878815133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3595507982866479353680709 674157746787464878815133)
  ·
    refine ⟨252809155045299329555675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 674157746787464878815133 252809155045299329555675)
    ·
      refine ⟨379213732567948994333513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252809155045299329555675 379213732567948994333513)
      ·
        refine ⟨284410299425961745750135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 379213732567948994333513 284410299425961745750135)
        ·
          refine ⟨426615449138942618625203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284410299425961745750135 426615449138942618625203)
          ·
            refine ⟨639923173708413927937805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426615449138942618625203 639923173708413927937805)
            ·
              refine ⟨239971190140655222976677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 639923173708413927937805 239971190140655222976677)
              ·
                refine ⟨44994598151372854308127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 239971190140655222976677 44994598151372854308127)
                ·
                  rfl

theorem cell19_147870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_147870 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_147870 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_147870 prefixEnd_147870 := by exact prefixLift 147870
  have htrace : WordTrace (prefixWord ++ tailWord_147870) baseStart_147870 baseEnd_147870 := by
    simpa [prefixWord, tailWord_147870, baseEnd_147870] using wordTrace_append hprefix tailTrace_147870
  have hstable : (prefixWord ++ tailWord_147870).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147870).length < 2 ^ (prefixWord ++ tailWord_147870).sum := by decide
  have hdescent : baseEnd_147870 < baseStart_147870 := by decide
  rcases family_descends (prefixWord ++ tailWord_147870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147872 : List Nat := [2, 1, 1, 4, 1, 5, 1, 4]
def baseStart_147872 : Nat := 118140960795 + 147872 * 2 ^ 59
def prefixEnd_147872 : Nat := 4983230072969 + 3 ^ 40 * 147872 * 2
def baseEnd_147872 : Nat := 44995206721037442263677

theorem tailTrace_147872 : CollatzResearch.WordTrace tailWord_147872 prefixEnd_147872 44995206721037442263677 := by
  unfold tailWord_147872
  simp only [CollatzResearch.WordTrace]
  refine ⟨2696667460146236686046935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3595556613528315581395913 2696667460146236686046935)
  ·
    refine ⟨4045001190219355029070403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2696667460146236686046935 4045001190219355029070403)
    ·
      refine ⟨6067501785329032543605605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4045001190219355029070403 6067501785329032543605605)
      ·
        refine ⟨1137656584749193601926051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6067501785329032543605605 1137656584749193601926051)
        ·
          refine ⟨1706484877123790402889077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1137656584749193601926051 1706484877123790402889077)
          ·
            refine ⟨159982957230355350270851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1706484877123790402889077 159982957230355350270851)
            ·
              refine ⟨239974435845533025406277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159982957230355350270851 239974435845533025406277)
              ·
                refine ⟨44995206721037442263677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 239974435845533025406277 44995206721037442263677)
                ·
                  rfl

theorem cell19_147872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 4].length) (baseStart_147872 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_147872 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_147872 prefixEnd_147872 := by exact prefixLift 147872
  have htrace : WordTrace (prefixWord ++ tailWord_147872) baseStart_147872 baseEnd_147872 := by
    simpa [prefixWord, tailWord_147872, baseEnd_147872] using wordTrace_append hprefix tailTrace_147872
  have hstable : (prefixWord ++ tailWord_147872).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147872).length < 2 ^ (prefixWord ++ tailWord_147872).sum := by decide
  have hdescent : baseEnd_147872 < baseStart_147872 := by decide
  rcases family_descends (prefixWord ++ tailWord_147872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147912 : List Nat := [2, 1, 3, 1, 3, 3, 6]
def baseStart_147912 : Nat := 118140960795 + 147912 * 2 ^ 59
def prefixEnd_147912 : Nat := 4983230072969 + 3 ^ 40 * 147912 * 2
def baseEnd_147912 : Nat := 15002459371443067124893

theorem tailTrace_147912 : CollatzResearch.WordTrace tailWord_147912 prefixEnd_147912 15002459371443067124893 := by
  unfold tailWord_147912
  simp only [CollatzResearch.WordTrace]
  refine ⟨2697396920073780101774995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3596529226765040135699993 2697396920073780101774995)
  ·
    refine ⟨4046095380110670152662493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2697396920073780101774995 4046095380110670152662493)
    ·
      refine ⟨1517285767541501307248435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4046095380110670152662493 1517285767541501307248435)
      ·
        refine ⟨2275928651312251960872653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1517285767541501307248435 2275928651312251960872653)
        ·
          refine ⟨853473244242094485327245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2275928651312251960872653 853473244242094485327245)
          ·
            refine ⟨320052466590785431997717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 853473244242094485327245 320052466590785431997717)
            ·
              refine ⟨15002459371443067124893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 320052466590785431997717 15002459371443067124893)
              ·
                rfl

theorem cell19_147912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 6].length) (baseStart_147912 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_147912 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_147912 prefixEnd_147912 := by exact prefixLift 147912
  have htrace : WordTrace (prefixWord ++ tailWord_147912) baseStart_147912 baseEnd_147912 := by
    simpa [prefixWord, tailWord_147912, baseEnd_147912] using wordTrace_append hprefix tailTrace_147912
  have hstable : (prefixWord ++ tailWord_147912).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147912).length < 2 ^ (prefixWord ++ tailWord_147912).sum := by decide
  have hdescent : baseEnd_147912 < baseStart_147912 := by decide
  rcases family_descends (prefixWord ++ tailWord_147912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147946 : List Nat := [3, 1, 3, 1, 3, 3, 2, 3]
def baseStart_147946 : Nat := 118140960795 + 147946 * 2 ^ 59
def prefixEnd_147946 : Nat := 4983230072969 + 3 ^ 40 * 147946 * 2
def baseEnd_147946 : Nat := 45017723798627196619031

theorem tailTrace_147946 : CollatzResearch.WordTrace tailWord_147946 prefixEnd_147946 45017723798627196619031 := by
  unfold tailWord_147946
  simp only [CollatzResearch.WordTrace]
  refine ⟨1349008480506096002571923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3597355948016256006858461 1349008480506096002571923)
  ·
    refine ⟨2023512720759144003857885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1349008480506096002571923 2023512720759144003857885)
    ·
      refine ⟨758817270284679001446707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2023512720759144003857885 758817270284679001446707)
      ·
        refine ⟨1138225905427018502170061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 758817270284679001446707 1138225905427018502170061)
        ·
          refine ⟨426834714535131938313773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1138225905427018502170061 426834714535131938313773)
          ·
            refine ⟨160063017950674476867665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 426834714535131938313773 160063017950674476867665)
            ·
              refine ⟨120047263463005857650749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160063017950674476867665 120047263463005857650749)
              ·
                refine ⟨45017723798627196619031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120047263463005857650749 45017723798627196619031)
                ·
                  rfl

theorem cell19_147946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_147946 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_147946 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_147946 prefixEnd_147946 := by exact prefixLift 147946
  have htrace : WordTrace (prefixWord ++ tailWord_147946) baseStart_147946 baseEnd_147946 := by
    simpa [prefixWord, tailWord_147946, baseEnd_147946] using wordTrace_append hprefix tailTrace_147946
  have hstable : (prefixWord ++ tailWord_147946).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147946).length < 2 ^ (prefixWord ++ tailWord_147946).sum := by decide
  have hdescent : baseEnd_147946 < baseStart_147946 := by decide
  rcases family_descends (prefixWord ++ tailWord_147946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147969 : List Nat := [1, 2, 4, 1, 3, 1, 7]
def baseStart_147969 : Nat := 118140960795 + 147969 * 2 ^ 59
def prefixEnd_147969 : Nat := 4983230072969 + 3 ^ 40 * 147969 * 2
def baseEnd_147969 : Nat := 15008240783256652702619

theorem tailTrace_147969 : CollatzResearch.WordTrace tailWord_147969 prefixEnd_147969 15008240783256652702619 := by
  unfold tailWord_147969
  simp only [CollatzResearch.WordTrace]
  refine ⟨5396872800941058938374961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3597915200627372625583307 5396872800941058938374961)
  ·
    refine ⟨4047654600705794203781221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5396872800941058938374961 4047654600705794203781221)
    ·
      refine ⟨758935237632336413208979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4047654600705794203781221 758935237632336413208979)
      ·
        refine ⟨1138402856448504619813469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 758935237632336413208979 1138402856448504619813469)
        ·
          refine ⟨426901071168189232430051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1138402856448504619813469 426901071168189232430051)
          ·
            refine ⟨640351606752283848645077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426901071168189232430051 640351606752283848645077)
            ·
              refine ⟨15008240783256652702619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 640351606752283848645077 15008240783256652702619)
              ·
                rfl

theorem cell19_147969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 7].length) (baseStart_147969 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_147969 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_147969 prefixEnd_147969 := by exact prefixLift 147969
  have htrace : WordTrace (prefixWord ++ tailWord_147969) baseStart_147969 baseEnd_147969 := by
    simpa [prefixWord, tailWord_147969, baseEnd_147969] using wordTrace_append hprefix tailTrace_147969
  have hstable : (prefixWord ++ tailWord_147969).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147969).length < 2 ^ (prefixWord ++ tailWord_147969).sum := by decide
  have hdescent : baseEnd_147969 < baseStart_147969 := by decide
  rcases family_descends (prefixWord ++ tailWord_147969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148060 : List Nat := [2, 2, 4, 1, 3, 1, 3, 3]
def baseStart_148060 : Nat := 118140960795 + 148060 * 2 ^ 59
def prefixEnd_148060 : Nat := 4983230072969 + 3 ^ 40 * 148060 * 2
def baseEnd_148060 : Nat := 45052412269508710085387

theorem tailTrace_148060 : CollatzResearch.WordTrace tailWord_148060 prefixEnd_148060 45052412269508710085387 := by
  unfold tailWord_148060
  simp only [CollatzResearch.WordTrace]
  refine ⟨2700095921805690739968817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3600127895740920986625089 2700095921805690739968817)
  ·
    refine ⟨2025071941354268054976613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2700095921805690739968817 2025071941354268054976613)
    ·
      refine ⟨379700989003925260308115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2025071941354268054976613 379700989003925260308115)
      ·
        refine ⟨569551483505887890462173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379700989003925260308115 569551483505887890462173)
        ·
          refine ⟨213581806314707958923315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 569551483505887890462173 213581806314707958923315)
          ·
            refine ⟨320372709472061938384973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213581806314707958923315 320372709472061938384973)
            ·
              refine ⟨120139766052023226894365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 320372709472061938384973 120139766052023226894365)
              ·
                refine ⟨45052412269508710085387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120139766052023226894365 45052412269508710085387)
                ·
                  rfl

theorem cell19_148060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 3].length) (baseStart_148060 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_148060 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_148060 prefixEnd_148060 := by exact prefixLift 148060
  have htrace : WordTrace (prefixWord ++ tailWord_148060) baseStart_148060 baseEnd_148060 := by
    simpa [prefixWord, tailWord_148060, baseEnd_148060] using wordTrace_append hprefix tailTrace_148060
  have hstable : (prefixWord ++ tailWord_148060).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148060).length < 2 ^ (prefixWord ++ tailWord_148060).sum := by decide
  have hdescent : baseEnd_148060 < baseStart_148060 := by decide
  rcases family_descends (prefixWord ++ tailWord_148060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148159 : List Nat := [1, 1, 2, 2, 2, 5, 2, 4]
def baseStart_148159 : Nat := 118140960795 + 148159 * 2 ^ 59
def prefixEnd_148159 : Nat := 4983230072969 + 3 ^ 40 * 148159 * 2
def baseEnd_148159 : Nat := 45082536467905813885117

theorem tailTrace_148159 : CollatzResearch.WordTrace tailWord_148159 prefixEnd_148159 45082536467905813885117 := by
  unfold tailWord_148159
  simp only [CollatzResearch.WordTrace]
  refine ⟨5403802670252721387791531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3602535113501814258527687 5403802670252721387791531)
  ·
    refine ⟨8105704005379082081687297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5403802670252721387791531 8105704005379082081687297)
    ·
      refine ⟨6079278004034311561265473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8105704005379082081687297 6079278004034311561265473)
      ·
        refine ⟨4559458503025733670949105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6079278004034311561265473 4559458503025733670949105)
        ·
          refine ⟨3419593877269300253211829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4559458503025733670949105 3419593877269300253211829)
          ·
            refine ⟨320586925993996898738609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3419593877269300253211829 320586925993996898738609)
            ·
              refine ⟨240440194495497674053957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 320586925993996898738609 240440194495497674053957)
              ·
                refine ⟨45082536467905813885117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 240440194495497674053957 45082536467905813885117)
                ·
                  rfl

theorem cell19_148159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 4].length) (baseStart_148159 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_148159 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_148159 prefixEnd_148159 := by exact prefixLift 148159
  have htrace : WordTrace (prefixWord ++ tailWord_148159) baseStart_148159 baseEnd_148159 := by
    simpa [prefixWord, tailWord_148159, baseEnd_148159] using wordTrace_append hprefix tailTrace_148159
  have hstable : (prefixWord ++ tailWord_148159).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148159).length < 2 ^ (prefixWord ++ tailWord_148159).sum := by decide
  have hdescent : baseEnd_148159 < baseStart_148159 := by decide
  rcases family_descends (prefixWord ++ tailWord_148159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148199 : List Nat := [1, 1, 5, 12]
def baseStart_148199 : Nat := 118140960795 + 148199 * 2 ^ 59
def prefixEnd_148199 : Nat := 4983230072969 + 3 ^ 40 * 148199 * 2
def baseEnd_148199 : Nat := 556724788409846580199

theorem tailTrace_148199 : CollatzResearch.WordTrace tailWord_148199 prefixEnd_148199 556724788409846580199 := by
  unfold tailWord_148199
  simp only [CollatzResearch.WordTrace]
  refine ⟨5405261590107808219247651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3603507726738538812831767 5405261590107808219247651)
  ·
    refine ⟨8107892385161712328871477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5405261590107808219247651 8107892385161712328871477)
    ·
      refine ⟨760114911108910530831701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8107892385161712328871477 760114911108910530831701)
      ·
        refine ⟨556724788409846580199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 760114911108910530831701 556724788409846580199)
        ·
          rfl

theorem cell19_148199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 12].length) (baseStart_148199 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_148199 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_148199 prefixEnd_148199 := by exact prefixLift 148199
  have htrace : WordTrace (prefixWord ++ tailWord_148199) baseStart_148199 baseEnd_148199 := by
    simpa [prefixWord, tailWord_148199, baseEnd_148199] using wordTrace_append hprefix tailTrace_148199
  have hstable : (prefixWord ++ tailWord_148199).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148199).length < 2 ^ (prefixWord ++ tailWord_148199).sum := by decide
  have hdescent : baseEnd_148199 < baseStart_148199 := by decide
  rcases family_descends (prefixWord ++ tailWord_148199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148286 : List Nat := [4, 2, 1, 2, 4, 1, 2, 3]
def baseStart_148286 : Nat := 118140960795 + 148286 * 2 ^ 59
def prefixEnd_148286 : Nat := 4983230072969 + 3 ^ 40 * 148286 * 2
def baseEnd_148286 : Nat := 45121180641607149062549

theorem tailTrace_148286 : CollatzResearch.WordTrace tailWord_148286 prefixEnd_148286 45121180641607149062549 := by
  unfold tailWord_148286
  simp only [CollatzResearch.WordTrace]
  refine ⟨676054342599077759708089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3605623160528414718443141 676054342599077759708089)
  ·
    refine ⟨507040756949308319781067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 676054342599077759708089 507040756949308319781067)
    ·
      refine ⟨760561135423962479671601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 507040756949308319781067 760561135423962479671601)
      ·
        refine ⟨570420851567971859753701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 760561135423962479671601 570420851567971859753701)
        ·
          refine ⟨106953909668994723703819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 570420851567971859753701 106953909668994723703819)
          ·
            refine ⟨160430864503492085555729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106953909668994723703819 160430864503492085555729)
            ·
              refine ⟨120323148377619064166797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160430864503492085555729 120323148377619064166797)
              ·
                refine ⟨45121180641607149062549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120323148377619064166797 45121180641607149062549)
                ·
                  rfl

theorem cell19_148286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_148286 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_148286 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_148286 prefixEnd_148286 := by exact prefixLift 148286
  have htrace : WordTrace (prefixWord ++ tailWord_148286) baseStart_148286 baseEnd_148286 := by
    simpa [prefixWord, tailWord_148286, baseEnd_148286] using wordTrace_append hprefix tailTrace_148286
  have hstable : (prefixWord ++ tailWord_148286).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148286).length < 2 ^ (prefixWord ++ tailWord_148286).sum := by decide
  have hdescent : baseEnd_148286 < baseStart_148286 := by decide
  rcases family_descends (prefixWord ++ tailWord_148286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148311 : List Nat := [1, 1, 3, 2, 4, 3, 5]
def baseStart_148311 : Nat := 118140960795 + 148311 * 2 ^ 59
def prefixEnd_148311 : Nat := 4983230072969 + 3 ^ 40 * 148311 * 2
def baseEnd_148311 : Nat := 15042929254138166168975

theorem tailTrace_148311 : CollatzResearch.WordTrace tailWord_148311 prefixEnd_148311 15042929254138166168975 := by
  unfold tailWord_148311
  simp only [CollatzResearch.WordTrace]
  refine ⟨5409346565702051347324787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3606231043801367564883191 5409346565702051347324787)
  ·
    refine ⟨8114019848553077020987181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5409346565702051347324787 8114019848553077020987181)
    ·
      refine ⟨3042757443207403882870193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8114019848553077020987181 3042757443207403882870193)
      ·
        refine ⟨2282068082405552912152645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3042757443207403882870193 2282068082405552912152645)
        ·
          refine ⟨427887765451041171028621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2282068082405552912152645 427887765451041171028621)
          ·
            refine ⟨160457912044140439135733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 427887765451041171028621 160457912044140439135733)
            ·
              refine ⟨15042929254138166168975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 160457912044140439135733 15042929254138166168975)
              ·
                rfl

theorem cell19_148311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 5].length) (baseStart_148311 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_148311 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_148311 prefixEnd_148311 := by exact prefixLift 148311
  have htrace : WordTrace (prefixWord ++ tailWord_148311) baseStart_148311 baseEnd_148311 := by
    simpa [prefixWord, tailWord_148311, baseEnd_148311] using wordTrace_append hprefix tailTrace_148311
  have hstable : (prefixWord ++ tailWord_148311).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148311).length < 2 ^ (prefixWord ++ tailWord_148311).sum := by decide
  have hdescent : baseEnd_148311 < baseStart_148311 := by decide
  rcases family_descends (prefixWord ++ tailWord_148311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148313 : List Nat := [1, 2, 1, 2, 2, 4, 7]
def baseStart_148313 : Nat := 118140960795 + 148313 * 2 ^ 59
def prefixEnd_148313 : Nat := 4983230072969 + 3 ^ 40 * 148313 * 2
def baseEnd_148313 : Nat := 15043132110693028820825

theorem tailTrace_148313 : CollatzResearch.WordTrace tailWord_148313 prefixEnd_148313 15043132110693028820825 := by
  unfold tailWord_148313
  simp only [CollatzResearch.WordTrace]
  refine ⟨5409419511694805688897593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3606279674463203792598395 5409419511694805688897593)
  ·
    refine ⟨4057064633771104266673195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5409419511694805688897593 4057064633771104266673195)
    ·
      refine ⟨6085596950656656400009793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4057064633771104266673195 6085596950656656400009793)
      ·
        refine ⟨4564197712992492300007345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6085596950656656400009793 4564197712992492300007345)
        ·
          refine ⟨3423148284744369225005509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4564197712992492300007345 3423148284744369225005509)
          ·
            refine ⟨641840303389569229688533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3423148284744369225005509 641840303389569229688533)
            ·
              refine ⟨15043132110693028820825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 641840303389569229688533 15043132110693028820825)
              ·
                rfl

theorem cell19_148313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 7].length) (baseStart_148313 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_148313 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_148313 prefixEnd_148313 := by exact prefixLift 148313
  have htrace : WordTrace (prefixWord ++ tailWord_148313) baseStart_148313 baseEnd_148313 := by
    simpa [prefixWord, tailWord_148313, baseEnd_148313] using wordTrace_append hprefix tailTrace_148313
  have hstable : (prefixWord ++ tailWord_148313).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148313).length < 2 ^ (prefixWord ++ tailWord_148313).sum := by decide
  have hdescent : baseEnd_148313 < baseStart_148313 := by decide
  rcases family_descends (prefixWord ++ tailWord_148313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148351 : List Nat := [1, 1, 2, 2, 1, 1, 6, 5]
def baseStart_148351 : Nat := 118140960795 + 148351 * 2 ^ 59
def prefixEnd_148351 : Nat := 4983230072969 + 3 ^ 40 * 148351 * 2
def baseEnd_148351 : Nat := 45140959155706257617927

theorem tailTrace_148351 : CollatzResearch.WordTrace tailWord_148351 prefixEnd_148351 45140959155706257617927 := by
  unfold tailWord_148351
  simp only [CollatzResearch.WordTrace]
  refine ⟨5410805485557138178780907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3607203657038092119187271 5410805485557138178780907)
  ·
    refine ⟨8116208228335707268171361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5410805485557138178780907 8116208228335707268171361)
    ·
      refine ⟨6087156171251780451128521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8116208228335707268171361 6087156171251780451128521)
      ·
        refine ⟨4565367128438835338346391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6087156171251780451128521 4565367128438835338346391)
        ·
          refine ⟨6848050692658253007519587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4565367128438835338346391 6848050692658253007519587)
          ·
            refine ⟨10272076038987379511279381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6848050692658253007519587 10272076038987379511279381)
            ·
              refine ⟨481503564327533414591221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10272076038987379511279381 481503564327533414591221)
              ·
                refine ⟨45140959155706257617927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 481503564327533414591221 45140959155706257617927)
                ·
                  rfl

theorem cell19_148351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 5].length) (baseStart_148351 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_148351 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_148351 prefixEnd_148351 := by exact prefixLift 148351
  have htrace : WordTrace (prefixWord ++ tailWord_148351) baseStart_148351 baseEnd_148351 := by
    simpa [prefixWord, tailWord_148351, baseEnd_148351] using wordTrace_append hprefix tailTrace_148351
  have hstable : (prefixWord ++ tailWord_148351).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148351).length < 2 ^ (prefixWord ++ tailWord_148351).sum := by decide
  have hdescent : baseEnd_148351 < baseStart_148351 := by decide
  rcases family_descends (prefixWord ++ tailWord_148351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148385 : List Nat := [1, 2, 3, 4, 1, 3, 1, 4]
def baseStart_148385 : Nat := 118140960795 + 148385 * 2 ^ 59
def prefixEnd_148385 : Nat := 4983230072969 + 3 ^ 40 * 148385 * 2
def baseEnd_148385 : Nat := 45151304840004252862279

theorem tailTrace_148385 : CollatzResearch.WordTrace tailWord_148385 prefixEnd_148385 45151304840004252862279 := by
  unfold tailWord_148385
  simp only [CollatzResearch.WordTrace]
  refine ⟨5412045567433961985518609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3608030378289307990345739 5412045567433961985518609)
  ·
    refine ⟨4059034175575471489138957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5412045567433961985518609 4059034175575471489138957)
    ·
      refine ⟨1522137815840801808427109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4059034175575471489138957 1522137815840801808427109)
      ·
        refine ⟨285400840470150339080083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1522137815840801808427109 285400840470150339080083)
        ·
          refine ⟨428101260705225508620125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285400840470150339080083 428101260705225508620125)
          ·
            refine ⟨160537972764459565732547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 428101260705225508620125 160537972764459565732547)
            ·
              refine ⟨240806959146689348598821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160537972764459565732547 240806959146689348598821)
              ·
                refine ⟨45151304840004252862279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 240806959146689348598821 45151304840004252862279)
                ·
                  rfl

theorem cell19_148385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 4].length) (baseStart_148385 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_148385 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_148385 prefixEnd_148385 := by exact prefixLift 148385
  have htrace : WordTrace (prefixWord ++ tailWord_148385) baseStart_148385 baseEnd_148385 := by
    simpa [prefixWord, tailWord_148385, baseEnd_148385] using wordTrace_append hprefix tailTrace_148385
  have hstable : (prefixWord ++ tailWord_148385).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148385).length < 2 ^ (prefixWord ++ tailWord_148385).sum := by decide
  have hdescent : baseEnd_148385 < baseStart_148385 := by decide
  rcases family_descends (prefixWord ++ tailWord_148385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148427 : List Nat := [1, 1, 1, 1, 3, 6, 6]
def baseStart_148427 : Nat := 118140960795 + 148427 * 2 ^ 59
def prefixEnd_148427 : Nat := 4983230072969 + 3 ^ 40 * 148427 * 2
def baseEnd_148427 : Nat := 15054694934320199976277

theorem tailTrace_148427 : CollatzResearch.WordTrace tailWord_148427 prefixEnd_148427 15054694934320199976277 := by
  unfold tailWord_148427
  simp only [CollatzResearch.WordTrace]
  refine ⟨5413577433281803158547535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3609051622187868772365023 5413577433281803158547535)
  ·
    refine ⟨8120366149922704737821303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5413577433281803158547535 8120366149922704737821303)
    ·
      refine ⟨12180549224884057106731955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8120366149922704737821303 12180549224884057106731955)
      ·
        refine ⟨18270823837326085660097933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12180549224884057106731955 18270823837326085660097933)
        ·
          refine ⟨6851558938997282122536725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18270823837326085660097933 6851558938997282122536725)
          ·
            refine ⟨321166825265497599493909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6851558938997282122536725 321166825265497599493909)
            ·
              refine ⟨15054694934320199976277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 321166825265497599493909 15054694934320199976277)
              ·
                rfl

theorem cell19_148427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 6].length) (baseStart_148427 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_148427 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_148427 prefixEnd_148427 := by exact prefixLift 148427
  have htrace : WordTrace (prefixWord ++ tailWord_148427) baseStart_148427 baseEnd_148427 := by
    simpa [prefixWord, tailWord_148427, baseEnd_148427] using wordTrace_append hprefix tailTrace_148427
  have hstable : (prefixWord ++ tailWord_148427).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148427).length < 2 ^ (prefixWord ++ tailWord_148427).sum := by decide
  have hdescent : baseEnd_148427 < baseStart_148427 := by decide
  rcases family_descends (prefixWord ++ tailWord_148427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148463 : List Nat := [1, 1, 2, 1, 4, 3, 4, 3]
def baseStart_148463 : Nat := 118140960795 + 148463 * 2 ^ 59
def prefixEnd_148463 : Nat := 4983230072969 + 3 ^ 40 * 148463 * 2
def baseEnd_148463 : Nat := 45175039056923183128733

theorem tailTrace_148463 : CollatzResearch.WordTrace tailWord_148463 prefixEnd_148463 45175039056923183128733 := by
  unfold tailWord_148463
  simp only [CollatzResearch.WordTrace]
  refine ⟨5414890461151381306858043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3609926974100920871238695 5414890461151381306858043)
  ·
    refine ⟨8122335691727071960287065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5414890461151381306858043 8122335691727071960287065)
    ·
      refine ⟨6091751768795303970215299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8122335691727071960287065 6091751768795303970215299)
      ·
        refine ⟨9137627653192955955322949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6091751768795303970215299 9137627653192955955322949)
        ·
          refine ⟨1713305184973679241623053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9137627653192955955322949 1713305184973679241623053)
          ·
            refine ⟨642489444365129715608645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1713305184973679241623053 642489444365129715608645)
            ·
              refine ⟨120466770818461821676621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 642489444365129715608645 120466770818461821676621)
              ·
                refine ⟨45175039056923183128733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120466770818461821676621 45175039056923183128733)
                ·
                  rfl

theorem cell19_148463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 3].length) (baseStart_148463 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_148463 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_148463 prefixEnd_148463 := by exact prefixLift 148463
  have htrace : WordTrace (prefixWord ++ tailWord_148463) baseStart_148463 baseEnd_148463 := by
    simpa [prefixWord, tailWord_148463, baseEnd_148463] using wordTrace_append hprefix tailTrace_148463
  have hstable : (prefixWord ++ tailWord_148463).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148463).length < 2 ^ (prefixWord ++ tailWord_148463).sum := by decide
  have hdescent : baseEnd_148463 < baseStart_148463 := by decide
  rcases family_descends (prefixWord ++ tailWord_148463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148478 : List Nat := [4, 2, 2, 2, 3, 1, 5]
def baseStart_148478 : Nat := 118140960795 + 148478 * 2 ^ 59
def prefixEnd_148478 : Nat := 4983230072969 + 3 ^ 40 * 148478 * 2
def baseEnd_148478 : Nat := 15059867776469197598453

theorem tailTrace_148478 : CollatzResearch.WordTrace tailWord_148478 prefixEnd_148478 15059867776469197598453 := by
  unfold tailWord_148478
  simp only [CollatzResearch.WordTrace]
  refine ⟨676929694512129858581761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3610291704064692579102725 676929694512129858581761)
  ·
    refine ⟨507697270884097393936321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 676929694512129858581761 507697270884097393936321)
    ·
      refine ⟨380772953163073045452241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 507697270884097393936321 380772953163073045452241)
      ·
        refine ⟨285579714872304784089181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 380772953163073045452241 285579714872304784089181)
        ·
          refine ⟨107092393077114294033443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 285579714872304784089181 107092393077114294033443)
          ·
            refine ⟨160638589615671441050165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107092393077114294033443 160638589615671441050165)
            ·
              refine ⟨15059867776469197598453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 160638589615671441050165 15059867776469197598453)
              ·
                rfl

theorem cell19_148478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 5].length) (baseStart_148478 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_148478 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_148478 prefixEnd_148478 := by exact prefixLift 148478
  have htrace : WordTrace (prefixWord ++ tailWord_148478) baseStart_148478 baseEnd_148478 := by
    simpa [prefixWord, tailWord_148478, baseEnd_148478] using wordTrace_append hprefix tailTrace_148478
  have hstable : (prefixWord ++ tailWord_148478).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148478).length < 2 ^ (prefixWord ++ tailWord_148478).sum := by decide
  have hdescent : baseEnd_148478 < baseStart_148478 := by decide
  rcases family_descends (prefixWord ++ tailWord_148478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148501 : List Nat := [1, 3, 2, 1, 4, 2, 2, 4]
def baseStart_148501 : Nat := 118140960795 + 148501 * 2 ^ 59
def prefixEnd_148501 : Nat := 4983230072969 + 3 ^ 40 * 148501 * 2
def baseEnd_148501 : Nat := 45186601880550354284185

theorem tailTrace_148501 : CollatzResearch.WordTrace tailWord_148501 prefixEnd_148501 45186601880550354284185 := by
  unfold tailWord_148501
  simp only [CollatzResearch.WordTrace]
  refine ⟨5416276435013713796741357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3610850956675809197827571 5416276435013713796741357)
  ·
    refine ⟨2031103663130142673778009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5416276435013713796741357 2031103663130142673778009)
    ·
      refine ⟨1523327747347607005333507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2031103663130142673778009 1523327747347607005333507)
      ·
        refine ⟨2284991621021410508000261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1523327747347607005333507 2284991621021410508000261)
        ·
          refine ⟨428435928941514470250049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2284991621021410508000261 428435928941514470250049)
          ·
            refine ⟨321326946706135852687537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 428435928941514470250049 321326946706135852687537)
            ·
              refine ⟨240995210029601889515653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 321326946706135852687537 240995210029601889515653)
              ·
                refine ⟨45186601880550354284185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 240995210029601889515653 45186601880550354284185)
                ·
                  rfl

theorem cell19_148501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 4].length) (baseStart_148501 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_148501 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_148501 prefixEnd_148501 := by exact prefixLift 148501
  have htrace : WordTrace (prefixWord ++ tailWord_148501) baseStart_148501 baseEnd_148501 := by
    simpa [prefixWord, tailWord_148501, baseEnd_148501] using wordTrace_append hprefix tailTrace_148501
  have hstable : (prefixWord ++ tailWord_148501).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148501).length < 2 ^ (prefixWord ++ tailWord_148501).sum := by decide
  have hdescent : baseEnd_148501 < baseStart_148501 := by decide
  rcases family_descends (prefixWord ++ tailWord_148501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148541 : List Nat := [1, 4, 1, 3, 1, 9]
def baseStart_148541 : Nat := 118140960795 + 148541 * 2 ^ 59
def prefixEnd_148541 : Nat := 4983230072969 + 3 ^ 40 * 148541 * 2
def baseEnd_148541 : Nat := 5022085919315790377243

theorem tailTrace_148541 : CollatzResearch.WordTrace tailWord_148541 prefixEnd_148541 5022085919315790377243 := by
  unfold tailWord_148541
  simp only [CollatzResearch.WordTrace]
  refine ⟨5417735354868800628197477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3611823569912533752131651 5417735354868800628197477)
  ·
    refine ⟨1015825379037900117787027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5417735354868800628197477 1015825379037900117787027)
    ·
      refine ⟨1523738068556850176680541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1015825379037900117787027 1523738068556850176680541)
      ·
        refine ⟨571401775708818816255203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1523738068556850176680541 571401775708818816255203)
        ·
          refine ⟨857102663563228224382805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 571401775708818816255203 857102663563228224382805)
          ·
            refine ⟨5022085919315790377243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 857102663563228224382805 5022085919315790377243)
            ·
              rfl

theorem cell19_148541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 9].length) (baseStart_148541 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_148541 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_148541 prefixEnd_148541 := by exact prefixLift 148541
  have htrace : WordTrace (prefixWord ++ tailWord_148541) baseStart_148541 baseEnd_148541 := by
    simpa [prefixWord, tailWord_148541, baseEnd_148541] using wordTrace_append hprefix tailTrace_148541
  have hstable : (prefixWord ++ tailWord_148541).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148541).length < 2 ^ (prefixWord ++ tailWord_148541).sum := by decide
  have hdescent : baseEnd_148541 < baseStart_148541 := by decide
  rcases family_descends (prefixWord ++ tailWord_148541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148573 : List Nat := [1, 4, 4, 1, 2, 1, 3, 3]
def baseStart_148573 : Nat := 118140960795 + 148573 * 2 ^ 59
def prefixEnd_148573 : Nat := 4983230072969 + 3 ^ 40 * 148573 * 2
def baseEnd_148573 : Nat := 45208510388475520683989

theorem tailTrace_148573 : CollatzResearch.WordTrace tailWord_148573 prefixEnd_148573 45208510388475520683989 := by
  unfold tailWord_148573
  simp only [CollatzResearch.WordTrace]
  refine ⟨5418902490752870093362373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3612601660501913395574915 5418902490752870093362373)
  ·
    refine ⟨1016044217016163142505445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5418902490752870093362373 1016044217016163142505445)
    ·
      refine ⟨190508290690530589219771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1016044217016163142505445 190508290690530589219771)
      ·
        refine ⟨285762436035795883829657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190508290690530589219771 285762436035795883829657)
        ·
          refine ⟨214321827026846912872243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 285762436035795883829657 214321827026846912872243)
          ·
            refine ⟨321482740540270369308365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214321827026846912872243 321482740540270369308365)
            ·
              refine ⟨120556027702601388490637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 321482740540270369308365 120556027702601388490637)
              ·
                refine ⟨45208510388475520683989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120556027702601388490637 45208510388475520683989)
                ·
                  rfl

theorem cell19_148573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 3].length) (baseStart_148573 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_148573 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_148573 prefixEnd_148573 := by exact prefixLift 148573
  have htrace : WordTrace (prefixWord ++ tailWord_148573) baseStart_148573 baseEnd_148573 := by
    simpa [prefixWord, tailWord_148573, baseEnd_148573] using wordTrace_append hprefix tailTrace_148573
  have hstable : (prefixWord ++ tailWord_148573).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148573).length < 2 ^ (prefixWord ++ tailWord_148573).sum := by decide
  have hdescent : baseEnd_148573 < baseStart_148573 := by decide
  rcases family_descends (prefixWord ++ tailWord_148573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148632 : List Nat := [2, 1, 2, 4, 2, 3, 2, 3]
def baseStart_148632 : Nat := 118140960795 + 148632 * 2 ^ 59
def prefixEnd_148632 : Nat := 4983230072969 + 3 ^ 40 * 148632 * 2
def baseEnd_148632 : Nat := 45226463193580865372717

theorem tailTrace_148632 : CollatzResearch.WordTrace tailWord_148632 prefixEnd_148632 45226463193580865372717 := by
  unfold tailWord_148632
  simp only [CollatzResearch.WordTrace]
  refine ⟨2710527198769561584880075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3614036265026082113173433 2710527198769561584880075)
  ·
    refine ⟨4065790798154342377320113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2710527198769561584880075 4065790798154342377320113)
    ·
      refine ⟨3049343098615756782990085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4065790798154342377320113 3049343098615756782990085)
      ·
        refine ⟨571751830990454396810641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3049343098615756782990085 571751830990454396810641)
        ·
          refine ⟨428813873242840797607981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 571751830990454396810641 428813873242840797607981)
          ·
            refine ⟨160805202466065299102993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 428813873242840797607981 160805202466065299102993)
            ·
              refine ⟨120603901849548974327245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160805202466065299102993 120603901849548974327245)
              ·
                refine ⟨45226463193580865372717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120603901849548974327245 45226463193580865372717)
                ·
                  rfl

theorem cell19_148632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 3].length) (baseStart_148632 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_148632 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_148632 prefixEnd_148632 := by exact prefixLift 148632
  have htrace : WordTrace (prefixWord ++ tailWord_148632) baseStart_148632 baseEnd_148632 := by
    simpa [prefixWord, tailWord_148632, baseEnd_148632] using wordTrace_append hprefix tailTrace_148632
  have hstable : (prefixWord ++ tailWord_148632).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148632).length < 2 ^ (prefixWord ++ tailWord_148632).sum := by decide
  have hdescent : baseEnd_148632 < baseStart_148632 := by decide
  rcases family_descends (prefixWord ++ tailWord_148632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148634 : List Nat := [3, 1, 1, 5, 1, 2, 1, 5]
def baseStart_148634 : Nat := 118140960795 + 148634 * 2 ^ 59
def prefixEnd_148634 : Nat := 4983230072969 + 3 ^ 40 * 148634 * 2
def baseEnd_148634 : Nat := 45227071763245453328267

theorem tailTrace_148634 : CollatzResearch.WordTrace tailWord_148634 prefixEnd_148634 45227071763245453328267 := by
  unfold tailWord_148634
  simp only [CollatzResearch.WordTrace]
  refine ⟨1355281835882969377833239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3614084895687918340888637 1355281835882969377833239)
  ·
    refine ⟨2032922753824454066749859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1355281835882969377833239 2032922753824454066749859)
    ·
      refine ⟨3049384130736681100124789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2032922753824454066749859 3049384130736681100124789)
      ·
        refine ⟨285879762256563853136699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3049384130736681100124789 285879762256563853136699)
        ·
          refine ⟨428819643384845779705049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285879762256563853136699 428819643384845779705049)
          ·
            refine ⟨321614732538634334778787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 428819643384845779705049 321614732538634334778787)
            ·
              refine ⟨482422098807951502168181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321614732538634334778787 482422098807951502168181)
              ·
                refine ⟨45227071763245453328267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 482422098807951502168181 45227071763245453328267)
                ·
                  rfl

theorem cell19_148634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_148634 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_148634 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_148634 prefixEnd_148634 := by exact prefixLift 148634
  have htrace : WordTrace (prefixWord ++ tailWord_148634) baseStart_148634 baseEnd_148634 := by
    simpa [prefixWord, tailWord_148634, baseEnd_148634] using wordTrace_append hprefix tailTrace_148634
  have hstable : (prefixWord ++ tailWord_148634).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148634).length < 2 ^ (prefixWord ++ tailWord_148634).sum := by decide
  have hdescent : baseEnd_148634 < baseStart_148634 := by decide
  rcases family_descends (prefixWord ++ tailWord_148634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148672 : List Nat := [2, 1, 1, 2, 6, 1, 2, 4]
def baseStart_148672 : Nat := 118140960795 + 148672 * 2 ^ 59
def prefixEnd_148672 : Nat := 4983230072969 + 3 ^ 40 * 148672 * 2
def baseEnd_148672 : Nat := 45238634586872624483719

theorem tailTrace_148672 : CollatzResearch.WordTrace tailWord_148672 prefixEnd_148672 45238634586872624483719 := by
  unfold tailWord_148672
  simp only [CollatzResearch.WordTrace]
  refine ⟨2711256658697105000608135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3615008878262806667477513 2711256658697105000608135)
  ·
    refine ⟨4066884988045657500912203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2711256658697105000608135 4066884988045657500912203)
    ·
      refine ⟨6100327482068486251368305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4066884988045657500912203 6100327482068486251368305)
      ·
        refine ⟨4575245611551364688526229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6100327482068486251368305 4575245611551364688526229)
        ·
          refine ⟨214464638041470219774667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4575245611551364688526229 214464638041470219774667)
          ·
            refine ⟨321696957062205329662001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214464638041470219774667 321696957062205329662001)
            ·
              refine ⟨241272717796653997246501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 321696957062205329662001 241272717796653997246501)
              ·
                refine ⟨45238634586872624483719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 241272717796653997246501 45238634586872624483719)
                ·
                  rfl

theorem cell19_148672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 4].length) (baseStart_148672 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_148672 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_148672 prefixEnd_148672 := by exact prefixLift 148672
  have htrace : WordTrace (prefixWord ++ tailWord_148672) baseStart_148672 baseEnd_148672 := by
    simpa [prefixWord, tailWord_148672, baseEnd_148672] using wordTrace_append hprefix tailTrace_148672
  have hstable : (prefixWord ++ tailWord_148672).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148672).length < 2 ^ (prefixWord ++ tailWord_148672).sum := by decide
  have hdescent : baseEnd_148672 < baseStart_148672 := by decide
  rcases family_descends (prefixWord ++ tailWord_148672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148748 : List Nat := [2, 2, 1, 2, 2, 4, 3, 3]
def baseStart_148748 : Nat := 118140960795 + 148748 * 2 ^ 59
def prefixEnd_148748 : Nat := 4983230072969 + 3 ^ 40 * 148748 * 2
def baseEnd_148748 : Nat := 45261760234126966794623

theorem tailTrace_148748 : CollatzResearch.WordTrace tailWord_148748 prefixEnd_148748 45261760234126966794623 := by
  unfold tailWord_148748
  simp only [CollatzResearch.WordTrace]
  refine ⟨2712642632559437490491449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3616856843412583320655265 2712642632559437490491449)
  ·
    refine ⟨2034481974419578117868587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2712642632559437490491449 2034481974419578117868587)
    ·
      refine ⟨3051722961629367176802881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2034481974419578117868587 3051722961629367176802881)
      ·
        refine ⟨2288792221222025382602161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3051722961629367176802881 2288792221222025382602161)
        ·
          refine ⟨1716594165916519036951621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2288792221222025382602161 1716594165916519036951621)
          ·
            refine ⟨321861406109347319428429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1716594165916519036951621 321861406109347319428429)
            ·
              refine ⟨120698027291005244785661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 321861406109347319428429 120698027291005244785661)
              ·
                refine ⟨45261760234126966794623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120698027291005244785661 45261760234126966794623)
                ·
                  rfl

theorem cell19_148748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 3].length) (baseStart_148748 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_148748 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_148748 prefixEnd_148748 := by exact prefixLift 148748
  have htrace : WordTrace (prefixWord ++ tailWord_148748) baseStart_148748 baseEnd_148748 := by
    simpa [prefixWord, tailWord_148748, baseEnd_148748] using wordTrace_append hprefix tailTrace_148748
  have hstable : (prefixWord ++ tailWord_148748).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148748).length < 2 ^ (prefixWord ++ tailWord_148748).sum := by decide
  have hdescent : baseEnd_148748 < baseStart_148748 := by decide
  rcases family_descends (prefixWord ++ tailWord_148748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148807 : List Nat := [1, 1, 4, 1, 2, 4, 1, 5]
def baseStart_148807 : Nat := 118140960795 + 148807 * 2 ^ 59
def prefixEnd_148807 : Nat := 4983230072969 + 3 ^ 40 * 148807 * 2
def baseEnd_148807 : Nat := 45279713039232311483351

theorem tailTrace_148807 : CollatzResearch.WordTrace tailWord_148807 prefixEnd_148807 45279713039232311483351 := by
  unfold tailWord_148807
  simp only [CollatzResearch.WordTrace]
  refine ⟨5427437171905128057380675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3618291447936752038253783 5427437171905128057380675)
  ·
    refine ⟨8141155757857692086071013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5427437171905128057380675 8141155757857692086071013)
    ·
      refine ⟨1526466704598317266138315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8141155757857692086071013 1526466704598317266138315)
      ·
        refine ⟨2289700056897475899207473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1526466704598317266138315 2289700056897475899207473)
        ·
          refine ⟨1717275042673106924405605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2289700056897475899207473 1717275042673106924405605)
          ·
            refine ⟨321989070501207548326051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1717275042673106924405605 321989070501207548326051)
            ·
              refine ⟨482983605751811322489077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321989070501207548326051 482983605751811322489077)
              ·
                refine ⟨45279713039232311483351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 482983605751811322489077 45279713039232311483351)
                ·
                  rfl

theorem cell19_148807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 5].length) (baseStart_148807 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_148807 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_148807 prefixEnd_148807 := by exact prefixLift 148807
  have htrace : WordTrace (prefixWord ++ tailWord_148807) baseStart_148807 baseEnd_148807 := by
    simpa [prefixWord, tailWord_148807, baseEnd_148807] using wordTrace_append hprefix tailTrace_148807
  have hstable : (prefixWord ++ tailWord_148807).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148807).length < 2 ^ (prefixWord ++ tailWord_148807).sum := by decide
  have hdescent : baseEnd_148807 < baseStart_148807 := by decide
  rcases family_descends (prefixWord ++ tailWord_148807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148845 : List Nat := [1, 5, 1, 1, 1, 3, 1, 6]
def baseStart_148845 : Nat := 118140960795 + 148845 * 2 ^ 59
def prefixEnd_148845 : Nat := 4983230072969 + 3 ^ 40 * 148845 * 2
def baseEnd_148845 : Nat := 45291275862859482638803

theorem tailTrace_148845 : CollatzResearch.WordTrace tailWord_148845 prefixEnd_148845 45291275862859482638803 := by
  unfold tailWord_148845
  simp only [CollatzResearch.WordTrace]
  refine ⟨5428823145767460547263989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3619215430511640364842659 5428823145767460547263989)
  ·
    refine ⟨508952169915699426305999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5428823145767460547263989 508952169915699426305999)
    ·
      refine ⟨763428254873549139458999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 508952169915699426305999 763428254873549139458999)
      ·
        refine ⟨1145142382310323709188499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 763428254873549139458999 1145142382310323709188499)
        ·
          refine ⟨1717713573465485563782749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1145142382310323709188499 1717713573465485563782749)
          ·
            refine ⟨644142590049557086418531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1717713573465485563782749 644142590049557086418531)
            ·
              refine ⟨966213885074335629627797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 644142590049557086418531 966213885074335629627797)
              ·
                refine ⟨45291275862859482638803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 966213885074335629627797 45291275862859482638803)
                ·
                  rfl

theorem cell19_148845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 6].length) (baseStart_148845 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_148845 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_148845 prefixEnd_148845 := by exact prefixLift 148845
  have htrace : WordTrace (prefixWord ++ tailWord_148845) baseStart_148845 baseEnd_148845 := by
    simpa [prefixWord, tailWord_148845, baseEnd_148845] using wordTrace_append hprefix tailTrace_148845
  have hstable : (prefixWord ++ tailWord_148845).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148845).length < 2 ^ (prefixWord ++ tailWord_148845).sum := by decide
  have hdescent : baseEnd_148845 < baseStart_148845 := by decide
  rcases family_descends (prefixWord ++ tailWord_148845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148940 : List Nat := [2, 2, 1, 4, 2, 2, 6]
def baseStart_148940 : Nat := 118140960795 + 148940 * 2 ^ 59
def prefixEnd_148940 : Nat := 4983230072969 + 3 ^ 40 * 148940 * 2
def baseEnd_148940 : Nat := 15106727640642470175811

theorem tailTrace_148940 : CollatzResearch.WordTrace tailWord_148940 prefixEnd_148940 15106727640642470175811 := by
  unfold tailWord_148940
  simp only [CollatzResearch.WordTrace]
  refine ⟨2716144040211645885986137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3621525386948861181314849 2716144040211645885986137)
  ·
    refine ⟨2037108030158734414489603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2716144040211645885986137 2037108030158734414489603)
    ·
      refine ⟨3055662045238101621734405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2037108030158734414489603 3055662045238101621734405)
      ·
        refine ⟨572936633482144054075201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3055662045238101621734405 572936633482144054075201)
        ·
          refine ⟨429702475111608040556401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 572936633482144054075201 429702475111608040556401)
          ·
            refine ⟨322276856333706030417301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 429702475111608040556401 322276856333706030417301)
            ·
              refine ⟨15106727640642470175811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 322276856333706030417301 15106727640642470175811)
              ·
                rfl

theorem cell19_148940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 6].length) (baseStart_148940 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_148940 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_148940 prefixEnd_148940 := by exact prefixLift 148940
  have htrace : WordTrace (prefixWord ++ tailWord_148940) baseStart_148940 baseEnd_148940 := by
    simpa [prefixWord, tailWord_148940, baseEnd_148940] using wordTrace_append hprefix tailTrace_148940
  have hstable : (prefixWord ++ tailWord_148940).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148940).length < 2 ^ (prefixWord ++ tailWord_148940).sum := by decide
  have hdescent : baseEnd_148940 < baseStart_148940 := by decide
  rcases family_descends (prefixWord ++ tailWord_148940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148976 : List Nat := [2, 1, 1, 1, 3, 6, 2, 3]
def baseStart_148976 : Nat := 118140960795 + 148976 * 2 ^ 59
def prefixEnd_148976 : Nat := 4983230072969 + 3 ^ 40 * 148976 * 2
def baseEnd_148976 : Nat := 45331137175889993727335

theorem tailTrace_148976 : CollatzResearch.WordTrace tailWord_148976 prefixEnd_148976 45331137175889993727335 := by
  unfold tailWord_148976
  simp only [CollatzResearch.WordTrace]
  refine ⟨2716800554146434960141391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3622400738861913280188521 2716800554146434960141391)
  ·
    refine ⟨4075200831219652440212087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2716800554146434960141391 4075200831219652440212087)
    ·
      refine ⟨6112801246829478660318131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4075200831219652440212087 6112801246829478660318131)
      ·
        refine ⟨9169201870244217990477197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6112801246829478660318131 9169201870244217990477197)
        ·
          refine ⟨3438450701341581746428949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9169201870244217990477197 3438450701341581746428949)
          ·
            refine ⟨161177376625386644363857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3438450701341581746428949 161177376625386644363857)
            ·
              refine ⟨120883032469039983272893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161177376625386644363857 120883032469039983272893)
              ·
                refine ⟨45331137175889993727335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120883032469039983272893 45331137175889993727335)
                ·
                  rfl

theorem cell19_148976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 3].length) (baseStart_148976 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_148976 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_148976 prefixEnd_148976 := by exact prefixLift 148976
  have htrace : WordTrace (prefixWord ++ tailWord_148976) baseStart_148976 baseEnd_148976 := by
    simpa [prefixWord, tailWord_148976, baseEnd_148976] using wordTrace_append hprefix tailTrace_148976
  have hstable : (prefixWord ++ tailWord_148976).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148976).length < 2 ^ (prefixWord ++ tailWord_148976).sum := by decide
  have hdescent : baseEnd_148976 < baseStart_148976 := by decide
  rcases family_descends (prefixWord ++ tailWord_148976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149012 : List Nat := [2, 4, 3, 1, 2, 1, 2, 4]
def baseStart_149012 : Nat := 118140960795 + 149012 * 2 ^ 59
def prefixEnd_149012 : Nat := 4983230072969 + 3 ^ 40 * 149012 * 2
def baseEnd_149012 : Nat := 45342091429852576927237

theorem tailTrace_149012 : CollatzResearch.WordTrace tailWord_149012 prefixEnd_149012 45342091429852576927237 := by
  unfold tailWord_149012
  simp only [CollatzResearch.WordTrace]
  refine ⟨2717457068081224034296645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3623276090774965379062193 2717457068081224034296645)
  ·
    refine ⟨509523200265229506430621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2717457068081224034296645 509523200265229506430621)
    ·
      refine ⟨191071200099461064911483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 509523200265229506430621 191071200099461064911483)
      ·
        refine ⟨286606800149191597367225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191071200099461064911483 286606800149191597367225)
        ·
          refine ⟨214955100111893698025419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286606800149191597367225 214955100111893698025419)
          ·
            refine ⟨322432650167840547038129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214955100111893698025419 322432650167840547038129)
            ·
              refine ⟨241824487625880410278597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 322432650167840547038129 241824487625880410278597)
              ·
                refine ⟨45342091429852576927237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 241824487625880410278597 45342091429852576927237)
                ·
                  rfl

theorem cell19_149012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 4].length) (baseStart_149012 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_149012 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_149012 prefixEnd_149012 := by exact prefixLift 149012
  have htrace : WordTrace (prefixWord ++ tailWord_149012) baseStart_149012 baseEnd_149012 := by
    simpa [prefixWord, tailWord_149012, baseEnd_149012] using wordTrace_append hprefix tailTrace_149012
  have hstable : (prefixWord ++ tailWord_149012).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149012).length < 2 ^ (prefixWord ++ tailWord_149012).sum := by decide
  have hdescent : baseEnd_149012 < baseStart_149012 := by decide
  rcases family_descends (prefixWord ++ tailWord_149012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149069 : List Nat := [1, 6, 1, 1, 3, 2, 1, 4]
def baseStart_149069 : Nat := 118140960795 + 149069 * 2 ^ 59
def prefixEnd_149069 : Nat := 4983230072969 + 3 ^ 40 * 149069 * 2
def baseEnd_149069 : Nat := 45359435665293333660415

theorem tailTrace_149069 : CollatzResearch.WordTrace tailWord_149069 prefixEnd_149069 45359435665293333660415 := by
  unfold tailWord_149069
  simp only [CollatzResearch.WordTrace]
  refine ⟨5436993096955946803418261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3624662064637297868945507 5436993096955946803418261)
  ·
    refine ⟨254859051419810006410231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5436993096955946803418261 254859051419810006410231)
    ·
      refine ⟨382288577129715009615347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254859051419810006410231 382288577129715009615347)
      ·
        refine ⟨573432865694572514423021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382288577129715009615347 573432865694572514423021)
        ·
          refine ⟨215037324635464692908633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 573432865694572514423021 215037324635464692908633)
          ·
            refine ⟨161277993476598519681475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215037324635464692908633 161277993476598519681475)
            ·
              refine ⟨241916990214897779522213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161277993476598519681475 241916990214897779522213)
              ·
                refine ⟨45359435665293333660415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 241916990214897779522213 45359435665293333660415)
                ·
                  rfl

theorem cell19_149069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 4].length) (baseStart_149069 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_149069 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_149069 prefixEnd_149069 := by exact prefixLift 149069
  have htrace : WordTrace (prefixWord ++ tailWord_149069) baseStart_149069 baseEnd_149069 := by
    simpa [prefixWord, tailWord_149069, baseEnd_149069] using wordTrace_append hprefix tailTrace_149069
  have hstable : (prefixWord ++ tailWord_149069).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149069).length < 2 ^ (prefixWord ++ tailWord_149069).sum := by decide
  have hdescent : baseEnd_149069 < baseStart_149069 := by decide
  rcases family_descends (prefixWord ++ tailWord_149069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149113 : List Nat := [1, 2, 1, 3, 3, 1, 8]
def baseStart_149113 : Nat := 118140960795 + 149113 * 2 ^ 59
def prefixEnd_149113 : Nat := 4983230072969 + 3 ^ 40 * 149113 * 2
def baseEnd_149113 : Nat := 15124274732638089560839

theorem tailTrace_149113 : CollatzResearch.WordTrace tailWord_149113 prefixEnd_149113 15124274732638089560839 := by
  unfold tailWord_149113
  simp only [CollatzResearch.WordTrace]
  refine ⟨5438597908796542318019993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3625731939197694878679995 5438597908796542318019993)
  ·
    refine ⟨4078948431597406738514995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5438597908796542318019993 4078948431597406738514995)
    ·
      refine ⟨6118422647396110107772493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4078948431597406738514995 6118422647396110107772493)
      ·
        refine ⟨2294408492773541290414685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6118422647396110107772493 2294408492773541290414685)
        ·
          refine ⟨860403184790077983905507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2294408492773541290414685 860403184790077983905507)
          ·
            refine ⟨1290604777185116975858261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 860403184790077983905507 1290604777185116975858261)
            ·
              refine ⟨15124274732638089560839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1290604777185116975858261 15124274732638089560839)
              ·
                rfl

theorem cell19_149113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 8].length) (baseStart_149113 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_149113 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_149113 prefixEnd_149113 := by exact prefixLift 149113
  have htrace : WordTrace (prefixWord ++ tailWord_149113) baseStart_149113 baseEnd_149113 := by
    simpa [prefixWord, tailWord_149113, baseEnd_149113] using wordTrace_append hprefix tailTrace_149113
  have hstable : (prefixWord ++ tailWord_149113).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149113).length < 2 ^ (prefixWord ++ tailWord_149113).sum := by decide
  have hdescent : baseEnd_149113 < baseStart_149113 := by decide
  rcases family_descends (prefixWord ++ tailWord_149113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149132 : List Nat := [2, 2, 1, 2, 1, 1, 4, 6]
def baseStart_149132 : Nat := 118140960795 + 149132 * 2 ^ 59
def prefixEnd_149132 : Nat := 4983230072969 + 3 ^ 40 * 149132 * 2
def baseEnd_149132 : Nat := 45378605609727854260243

theorem tailTrace_149132 : CollatzResearch.WordTrace tailWord_149132 prefixEnd_149132 45378605609727854260243 := by
  unfold tailWord_149132
  simp only [CollatzResearch.WordTrace]
  refine ⟨2719645447863854281480825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3626193930485139041974433 2719645447863854281480825)
  ·
    refine ⟨2039734085897890711110619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2719645447863854281480825 2039734085897890711110619)
    ·
      refine ⟨3059601128846836066665929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2039734085897890711110619 3059601128846836066665929)
      ·
        refine ⟨2294700846635127049999447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3059601128846836066665929 2294700846635127049999447)
        ·
          refine ⟨3442051269952690574999171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2294700846635127049999447 3442051269952690574999171)
          ·
            refine ⟨5163076904929035862498757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3442051269952690574999171 5163076904929035862498757)
            ·
              refine ⟨968076919674194224218517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5163076904929035862498757 968076919674194224218517)
              ·
                refine ⟨45378605609727854260243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 968076919674194224218517 45378605609727854260243)
                ·
                  rfl

theorem cell19_149132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_149132 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_149132 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_149132 prefixEnd_149132 := by exact prefixLift 149132
  have htrace : WordTrace (prefixWord ++ tailWord_149132) baseStart_149132 baseEnd_149132 := by
    simpa [prefixWord, tailWord_149132, baseEnd_149132] using wordTrace_append hprefix tailTrace_149132
  have hstable : (prefixWord ++ tailWord_149132).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149132).length < 2 ^ (prefixWord ++ tailWord_149132).sum := by decide
  have hdescent : baseEnd_149132 < baseStart_149132 := by decide
  rcases family_descends (prefixWord ++ tailWord_149132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149170 : List Nat := [3, 2, 1, 1, 1, 2, 9]
def baseStart_149170 : Nat := 118140960795 + 149170 * 2 ^ 59
def prefixEnd_149170 : Nat := 4983230072969 + 3 ^ 40 * 149170 * 2
def baseEnd_149170 : Nat := 15130056144451675138565

theorem tailTrace_149170 : CollatzResearch.WordTrace tailWord_149170 prefixEnd_149170 15130056144451675138565 := by
  unfold tailWord_149170
  simp only [CollatzResearch.WordTrace]
  refine ⟨1360169217397510263211241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3627117913060027368563309 1360169217397510263211241)
  ·
    refine ⟨1020126913048132697408431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1360169217397510263211241 1020126913048132697408431)
    ·
      refine ⟨1530190369572199046112647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1020126913048132697408431 1530190369572199046112647)
      ·
        refine ⟨2295285554358298569168971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1530190369572199046112647 2295285554358298569168971)
        ·
          refine ⟨3442928331537447853753457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2295285554358298569168971 3442928331537447853753457)
          ·
            refine ⟨2582196248653085890315093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3442928331537447853753457 2582196248653085890315093)
            ·
              refine ⟨15130056144451675138565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2582196248653085890315093 15130056144451675138565)
              ·
                rfl

theorem cell19_149170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 9].length) (baseStart_149170 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_149170 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_149170 prefixEnd_149170 := by exact prefixLift 149170
  have htrace : WordTrace (prefixWord ++ tailWord_149170) baseStart_149170 baseEnd_149170 := by
    simpa [prefixWord, tailWord_149170, baseEnd_149170] using wordTrace_append hprefix tailTrace_149170
  have hstable : (prefixWord ++ tailWord_149170).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149170).length < 2 ^ (prefixWord ++ tailWord_149170).sum := by decide
  have hdescent : baseEnd_149170 < baseStart_149170 := by decide
  rcases family_descends (prefixWord ++ tailWord_149170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149208 : List Nat := [2, 1, 2, 2, 3, 1, 1, 7]
def baseStart_149208 : Nat := 118140960795 + 149208 * 2 ^ 59
def prefixEnd_149208 : Nat := 4983230072969 + 3 ^ 40 * 149208 * 2
def baseEnd_149208 : Nat := 45401731256982196571147

theorem tailTrace_149208 : CollatzResearch.WordTrace tailWord_149208 prefixEnd_149208 45401731256982196571147 := by
  unfold tailWord_149208
  simp only [CollatzResearch.WordTrace]
  refine ⟨2721031421726186771364139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3628041895634915695152185 2721031421726186771364139)
  ·
    refine ⟨4081547132589280157046209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2721031421726186771364139 4081547132589280157046209)
    ·
      refine ⟨3061160349441960117784657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4081547132589280157046209 3061160349441960117784657)
      ·
        refine ⟨2295870262081470088338493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3061160349441960117784657 2295870262081470088338493)
        ·
          refine ⟨860951348280551283126935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2295870262081470088338493 860951348280551283126935)
          ·
            refine ⟨1291427022420826924690403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 860951348280551283126935 1291427022420826924690403)
            ·
              refine ⟨1937140533631240387035605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1291427022420826924690403 1937140533631240387035605)
              ·
                refine ⟨45401731256982196571147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1937140533631240387035605 45401731256982196571147)
                ·
                  rfl

theorem cell19_149208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_149208 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_149208 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_149208 prefixEnd_149208 := by exact prefixLift 149208
  have htrace : WordTrace (prefixWord ++ tailWord_149208) baseStart_149208 baseEnd_149208 := by
    simpa [prefixWord, tailWord_149208, baseEnd_149208] using wordTrace_append hprefix tailTrace_149208
  have hstable : (prefixWord ++ tailWord_149208).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149208).length < 2 ^ (prefixWord ++ tailWord_149208).sum := by decide
  have hdescent : baseEnd_149208 < baseStart_149208 := by decide
  rcases family_descends (prefixWord ++ tailWord_149208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149223 : List Nat := [1, 1, 5, 4, 2, 6]
def baseStart_149223 : Nat := 118140960795 + 149223 * 2 ^ 59
def prefixEnd_149223 : Nat := 4983230072969 + 3 ^ 40 * 149223 * 2
def baseEnd_149223 : Nat := 5045143947718511804197

theorem tailTrace_149223 : CollatzResearch.WordTrace tailWord_149223 prefixEnd_149223 5045143947718511804197 := by
  unfold tailWord_149223
  simp only [CollatzResearch.WordTrace]
  refine ⟨5442609938398031104524323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3628406625598687403016215 5442609938398031104524323)
  ·
    refine ⟨8163914907597046656786485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5442609938398031104524323 8163914907597046656786485)
    ·
      refine ⟨765367022587223124073733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8163914907597046656786485 765367022587223124073733)
      ·
        refine ⟨143506316735104335763825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 765367022587223124073733 143506316735104335763825)
        ·
          refine ⟨107629737551328251822869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143506316735104335763825 107629737551328251822869)
          ·
            refine ⟨5045143947718511804197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 107629737551328251822869 5045143947718511804197)
            ·
              rfl

theorem cell19_149223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 6].length) (baseStart_149223 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_149223 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_149223 prefixEnd_149223 := by exact prefixLift 149223
  have htrace : WordTrace (prefixWord ++ tailWord_149223) baseStart_149223 baseEnd_149223 := by
    simpa [prefixWord, tailWord_149223, baseEnd_149223] using wordTrace_append hprefix tailTrace_149223
  have hstable : (prefixWord ++ tailWord_149223).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149223).length < 2 ^ (prefixWord ++ tailWord_149223).sum := by decide
  have hdescent : baseEnd_149223 < baseStart_149223 := by decide
  rcases family_descends (prefixWord ++ tailWord_149223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149278 : List Nat := [4, 3, 2, 2, 1, 1, 6]
def baseStart_149278 : Nat := 118140960795 + 149278 * 2 ^ 59
def prefixEnd_149278 : Nat := 4983230072969 + 3 ^ 40 * 149278 * 2
def baseEnd_149278 : Nat := 15141010398414258338467

theorem tailTrace_149278 : CollatzResearch.WordTrace tailWord_149278 prefixEnd_149278 15141010398414258338467 := by
  unfold tailWord_149278
  simp only [CollatzResearch.WordTrace]
  refine ⟨680576994149846937222061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3629743968799183665184325 680576994149846937222061)
  ·
    refine ⟨255216372806192601458273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 680576994149846937222061 255216372806192601458273)
    ·
      refine ⟨191412279604644451093705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255216372806192601458273 191412279604644451093705)
      ·
        refine ⟨143559209703483338320279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191412279604644451093705 143559209703483338320279)
        ·
          refine ⟨215338814555225007480419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143559209703483338320279 215338814555225007480419)
          ·
            refine ⟨323008221832837511220629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215338814555225007480419 323008221832837511220629)
            ·
              refine ⟨15141010398414258338467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 323008221832837511220629 15141010398414258338467)
              ·
                rfl

theorem cell19_149278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 6].length) (baseStart_149278 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_149278 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_149278 prefixEnd_149278 := by exact prefixLift 149278
  have htrace : WordTrace (prefixWord ++ tailWord_149278) baseStart_149278 baseEnd_149278 := by
    simpa [prefixWord, tailWord_149278, baseEnd_149278] using wordTrace_append hprefix tailTrace_149278
  have hstable : (prefixWord ++ tailWord_149278).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149278).length < 2 ^ (prefixWord ++ tailWord_149278).sum := by decide
  have hdescent : baseEnd_149278 < baseStart_149278 := by decide
  rcases family_descends (prefixWord ++ tailWord_149278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149320 : List Nat := [2, 1, 3, 1, 1, 4, 4, 3]
def baseStart_149320 : Nat := 118140960795 + 149320 * 2 ^ 59
def prefixEnd_149320 : Nat := 4983230072969 + 3 ^ 40 * 149320 * 2
def baseEnd_149320 : Nat := 45435811158199122081953

theorem tailTrace_149320 : CollatzResearch.WordTrace tailWord_149320 prefixEnd_149320 45435811158199122081953 := by
  unfold tailWord_149320
  simp only [CollatzResearch.WordTrace]
  refine ⟨2723073909523308335402707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3630765212697744447203609 2723073909523308335402707)
  ·
    refine ⟨4084610864284962503104061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2723073909523308335402707 4084610864284962503104061)
    ·
      refine ⟨1531729074106860938664023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4084610864284962503104061 1531729074106860938664023)
      ·
        refine ⟨2297593611160291407996035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1531729074106860938664023 2297593611160291407996035)
        ·
          refine ⟨3446390416740437111994053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2297593611160291407996035 3446390416740437111994053)
          ·
            refine ⟨646198203138831958498885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3446390416740437111994053 646198203138831958498885)
            ·
              refine ⟨121162163088530992218541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 646198203138831958498885 121162163088530992218541)
              ·
                refine ⟨45435811158199122081953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121162163088530992218541 45435811158199122081953)
                ·
                  rfl

theorem cell19_149320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 3].length) (baseStart_149320 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_149320 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_149320 prefixEnd_149320 := by exact prefixLift 149320
  have htrace : WordTrace (prefixWord ++ tailWord_149320) baseStart_149320 baseEnd_149320 := by
    simpa [prefixWord, tailWord_149320, baseEnd_149320] using wordTrace_append hprefix tailTrace_149320
  have hstable : (prefixWord ++ tailWord_149320).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149320).length < 2 ^ (prefixWord ++ tailWord_149320).sum := by decide
  have hdescent : baseEnd_149320 < baseStart_149320 := by decide
  rcases family_descends (prefixWord ++ tailWord_149320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149322 : List Nat := [3, 1, 2, 1, 1, 1, 5, 5]
def baseStart_149322 : Nat := 118140960795 + 149322 * 2 ^ 59
def prefixEnd_149322 : Nat := 4983230072969 + 3 ^ 40 * 149322 * 2
def baseEnd_149322 : Nat := 45436419727863710037503

theorem tailTrace_149322 : CollatzResearch.WordTrace tailWord_149322 prefixEnd_149322 45436419727863710037503 := by
  unfold tailWord_149322
  simp only [CollatzResearch.WordTrace]
  refine ⟨1361555191259842753094555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3630813843359580674918813 1361555191259842753094555)
  ·
    refine ⟨2042332786889764129641833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1361555191259842753094555 2042332786889764129641833)
    ·
      refine ⟨1531749590167323097231375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2042332786889764129641833 1531749590167323097231375)
      ·
        refine ⟨2297624385250984645847063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1531749590167323097231375 2297624385250984645847063)
        ·
          refine ⟨3446436577876476968770595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2297624385250984645847063 3446436577876476968770595)
          ·
            refine ⟨5169654866814715453155893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3446436577876476968770595 5169654866814715453155893)
            ·
              refine ⟨484655143763879573733365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5169654866814715453155893 484655143763879573733365)
              ·
                refine ⟨45436419727863710037503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 484655143763879573733365 45436419727863710037503)
                ·
                  rfl

theorem cell19_149322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_149322 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_149322 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_149322 prefixEnd_149322 := by exact prefixLift 149322
  have htrace : WordTrace (prefixWord ++ tailWord_149322) baseStart_149322 baseEnd_149322 := by
    simpa [prefixWord, tailWord_149322, baseEnd_149322] using wordTrace_append hprefix tailTrace_149322
  have hstable : (prefixWord ++ tailWord_149322).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149322).length < 2 ^ (prefixWord ++ tailWord_149322).sum := by decide
  have hdescent : baseEnd_149322 < baseStart_149322 := by decide
  rcases family_descends (prefixWord ++ tailWord_149322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149358 : List Nat := [4, 1, 2, 3, 1, 1, 1, 6]
def baseStart_149358 : Nat := 118140960795 + 149358 * 2 ^ 59
def prefixEnd_149358 : Nat := 4983230072969 + 3 ^ 40 * 149358 * 2
def baseEnd_149358 : Nat := 45447373981826293237405

theorem tailTrace_149358 : CollatzResearch.WordTrace tailWord_149358 prefixEnd_149358 45447373981826293237405 := by
  unfold tailWord_149358
  simp only [CollatzResearch.WordTrace]
  refine ⟨680941724113618645086091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3631689195272632773792485 680941724113618645086091)
  ·
    refine ⟨1021412586170427967629137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 680941724113618645086091 1021412586170427967629137)
    ·
      refine ⟨766059439627820975721853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1021412586170427967629137 766059439627820975721853)
      ·
        refine ⟨287272289860432865895695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 766059439627820975721853 287272289860432865895695)
        ·
          refine ⟨430908434790649298843543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287272289860432865895695 430908434790649298843543)
          ·
            refine ⟨646362652185973948265315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 430908434790649298843543 646362652185973948265315)
            ·
              refine ⟨969543978278960922397973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 646362652185973948265315 969543978278960922397973)
              ·
                refine ⟨45447373981826293237405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 969543978278960922397973 45447373981826293237405)
                ·
                  rfl

theorem cell19_149358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_149358 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_149358 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_149358 prefixEnd_149358 := by exact prefixLift 149358
  have htrace : WordTrace (prefixWord ++ tailWord_149358) baseStart_149358 baseEnd_149358 := by
    simpa [prefixWord, tailWord_149358, baseEnd_149358] using wordTrace_append hprefix tailTrace_149358
  have hstable : (prefixWord ++ tailWord_149358).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149358).length < 2 ^ (prefixWord ++ tailWord_149358).sum := by decide
  have hdescent : baseEnd_149358 < baseStart_149358 := by decide
  rcases family_descends (prefixWord ++ tailWord_149358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149379 : List Nat := [1, 1, 1, 3, 4, 2, 2, 5]
def baseStart_149379 : Nat := 118140960795 + 149379 * 2 ^ 59
def prefixEnd_149379 : Nat := 4983230072969 + 3 ^ 40 * 149379 * 2
def baseEnd_149379 : Nat := 45453763963304466770681

theorem tailTrace_149379 : CollatzResearch.WordTrace tailWord_149379 prefixEnd_149379 45453763963304466770681 := by
  unfold tailWord_149379
  simp only [CollatzResearch.WordTrace]
  refine ⟨5448299725832869747203191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3632199817221913164802127 5448299725832869747203191)
  ·
    refine ⟨8172449588749304620804787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5448299725832869747203191 8172449588749304620804787)
    ·
      refine ⟨12258674383123956931207181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8172449588749304620804787 12258674383123956931207181)
      ·
        refine ⟨4597002893671483849202693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12258674383123956931207181 4597002893671483849202693)
        ·
          refine ⟨861938042563403221725505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4597002893671483849202693 861938042563403221725505)
          ·
            refine ⟨646453531922552416294129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 861938042563403221725505 646453531922552416294129)
            ·
              refine ⟨484840148941914312220597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 646453531922552416294129 484840148941914312220597)
              ·
                refine ⟨45453763963304466770681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 484840148941914312220597 45453763963304466770681)
                ·
                  rfl

theorem cell19_149379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 5].length) (baseStart_149379 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_149379 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_149379 prefixEnd_149379 := by exact prefixLift 149379
  have htrace : WordTrace (prefixWord ++ tailWord_149379) baseStart_149379 baseEnd_149379 := by
    simpa [prefixWord, tailWord_149379, baseEnd_149379] using wordTrace_append hprefix tailTrace_149379
  have hstable : (prefixWord ++ tailWord_149379).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149379).length < 2 ^ (prefixWord ++ tailWord_149379).sum := by decide
  have hdescent : baseEnd_149379 < baseStart_149379 := by decide
  rcases family_descends (prefixWord ++ tailWord_149379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149415 : List Nat := [1, 1, 6, 1, 2, 1, 3, 4]
def baseStart_149415 : Nat := 118140960795 + 149415 * 2 ^ 59
def prefixEnd_149415 : Nat := 4983230072969 + 3 ^ 40 * 149415 * 2
def baseEnd_149415 : Nat := 45464718217267049970583

theorem tailTrace_149415 : CollatzResearch.WordTrace tailWord_149415 prefixEnd_149415 45464718217267049970583 := by
  unfold tailWord_149415
  simp only [CollatzResearch.WordTrace]
  refine ⟨5449612753702447895513699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3633075169134965263675799 5449612753702447895513699)
  ·
    refine ⟨8174419130553671843270549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5449612753702447895513699 8174419130553671843270549)
    ·
      refine ⟨383175896744703367653307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8174419130553671843270549 383175896744703367653307)
      ·
        refine ⟨574763845117055051479961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383175896744703367653307 574763845117055051479961)
        ·
          refine ⟨431072883837791288609971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 574763845117055051479961 431072883837791288609971)
          ·
            refine ⟨646609325756686932914957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431072883837791288609971 646609325756686932914957)
            ·
              refine ⟨242478497158757599843109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 646609325756686932914957 242478497158757599843109)
              ·
                refine ⟨45464718217267049970583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 242478497158757599843109 45464718217267049970583)
                ·
                  rfl

theorem cell19_149415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 4].length) (baseStart_149415 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_149415 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_149415 prefixEnd_149415 := by exact prefixLift 149415
  have htrace : WordTrace (prefixWord ++ tailWord_149415) baseStart_149415 baseEnd_149415 := by
    simpa [prefixWord, tailWord_149415, baseEnd_149415] using wordTrace_append hprefix tailTrace_149415
  have hstable : (prefixWord ++ tailWord_149415).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149415).length < 2 ^ (prefixWord ++ tailWord_149415).sum := by decide
  have hdescent : baseEnd_149415 < baseStart_149415 := by decide
  rcases family_descends (prefixWord ++ tailWord_149415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149485 : List Nat := [1, 5, 1, 4, 2, 1, 2, 3]
def baseStart_149485 : Nat := 118140960795 + 149485 * 2 ^ 59
def prefixEnd_149485 : Nat := 4983230072969 + 3 ^ 40 * 149485 * 2
def baseEnd_149485 : Nat := 45486018155527628414837

theorem tailTrace_149485 : CollatzResearch.WordTrace tailWord_149485 prefixEnd_149485 45486018155527628414837 := by
  unfold tailWord_149485
  simp only [CollatzResearch.WordTrace]
  refine ⟨5452165863448849850561909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3634777242299233233707939 5452165863448849850561909)
  ·
    refine ⟨511140549698329673490179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5452165863448849850561909 511140549698329673490179)
    ·
      refine ⟨766710824547494510235269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 511140549698329673490179 766710824547494510235269)
      ·
        refine ⟨143758279602655220669113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 766710824547494510235269 143758279602655220669113)
        ·
          refine ⟨107818709701991415501835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143758279602655220669113 107818709701991415501835)
          ·
            refine ⟨161728064552987123252753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107818709701991415501835 161728064552987123252753)
            ·
              refine ⟨121296048414740342439565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161728064552987123252753 121296048414740342439565)
              ·
                refine ⟨45486018155527628414837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121296048414740342439565 45486018155527628414837)
                ·
                  rfl

theorem cell19_149485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 3].length) (baseStart_149485 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_149485 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_149485 prefixEnd_149485 := by exact prefixLift 149485
  have htrace : WordTrace (prefixWord ++ tailWord_149485) baseStart_149485 baseEnd_149485 := by
    simpa [prefixWord, tailWord_149485, baseEnd_149485] using wordTrace_append hprefix tailTrace_149485
  have hstable : (prefixWord ++ tailWord_149485).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149485).length < 2 ^ (prefixWord ++ tailWord_149485).sum := by decide
  have hdescent : baseEnd_149485 < baseStart_149485 := by decide
  rcases family_descends (prefixWord ++ tailWord_149485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149489 : List Nat := [1, 2, 2, 2, 5, 2, 2, 3]
def baseStart_149489 : Nat := 118140960795 + 149489 * 2 ^ 59
def prefixEnd_149489 : Nat := 4983230072969 + 3 ^ 40 * 149489 * 2
def baseEnd_149489 : Nat := 45487235294856804325937

theorem tailTrace_149489 : CollatzResearch.WordTrace tailWord_149489 prefixEnd_149489 45487235294856804325937 := by
  unfold tailWord_149489
  simp only [CollatzResearch.WordTrace]
  refine ⟨5452311755434358533707521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3634874503622905689138347 5452311755434358533707521)
  ·
    refine ⟨4089233816575768900280641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5452311755434358533707521 4089233816575768900280641)
    ·
      refine ⟨3066925362431826675210481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4089233816575768900280641 3066925362431826675210481)
      ·
        refine ⟨2300194021823870006407861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3066925362431826675210481 2300194021823870006407861)
        ·
          refine ⟨215643189545987813100737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2300194021823870006407861 215643189545987813100737)
          ·
            refine ⟨161732392159490859825553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215643189545987813100737 161732392159490859825553)
            ·
              refine ⟨121299294119618144869165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161732392159490859825553 121299294119618144869165)
              ·
                refine ⟨45487235294856804325937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121299294119618144869165 45487235294856804325937)
                ·
                  rfl

theorem cell19_149489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 3].length) (baseStart_149489 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_149489 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_149489 prefixEnd_149489 := by exact prefixLift 149489
  have htrace : WordTrace (prefixWord ++ tailWord_149489) baseStart_149489 baseEnd_149489 := by
    simpa [prefixWord, tailWord_149489, baseEnd_149489] using wordTrace_append hprefix tailTrace_149489
  have hstable : (prefixWord ++ tailWord_149489).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149489).length < 2 ^ (prefixWord ++ tailWord_149489).sum := by decide
  have hdescent : baseEnd_149489 < baseStart_149489 := by decide
  rcases family_descends (prefixWord ++ tailWord_149489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149508 : List Nat := [2, 3, 2, 4, 1, 2, 5]
def baseStart_149508 : Nat := 118140960795 + 149508 * 2 ^ 59
def prefixEnd_149508 : Nat := 4983230072969 + 3 ^ 40 * 149508 * 2
def baseEnd_149508 : Nat := 15164338902223463301221

theorem tailTrace_149508 : CollatzResearch.WordTrace tailWord_149508 prefixEnd_149508 15164338902223463301221 := by
  unfold tailWord_149508
  simp only [CollatzResearch.WordTrace]
  refine ⟨2726502371182762389324589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3635336494910349852432785 2726502371182762389324589)
  ·
    refine ⟨1022438389193535895996721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2726502371182762389324589 1022438389193535895996721)
    ·
      refine ⟨766828791895151921997541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1022438389193535895996721 766828791895151921997541)
      ·
        refine ⟨143780398480340985374539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 766828791895151921997541 143780398480340985374539)
        ·
          refine ⟨215670597720511478061809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143780398480340985374539 215670597720511478061809)
          ·
            refine ⟨161752948290383608546357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215670597720511478061809 161752948290383608546357)
            ·
              refine ⟨15164338902223463301221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 161752948290383608546357 15164338902223463301221)
              ·
                rfl

theorem cell19_149508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 5].length) (baseStart_149508 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_149508 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_149508 prefixEnd_149508 := by exact prefixLift 149508
  have htrace : WordTrace (prefixWord ++ tailWord_149508) baseStart_149508 baseEnd_149508 := by
    simpa [prefixWord, tailWord_149508, baseEnd_149508] using wordTrace_append hprefix tailTrace_149508
  have hstable : (prefixWord ++ tailWord_149508).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149508).length < 2 ^ (prefixWord ++ tailWord_149508).sum := by decide
  have hdescent : baseEnd_149508 < baseStart_149508 := by decide
  rcases family_descends (prefixWord ++ tailWord_149508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149569 : List Nat := [1, 2, 5, 1, 2, 8]
def baseStart_149569 : Nat := 118140960795 + 149569 * 2 ^ 59
def prefixEnd_149569 : Nat := 4983230072969 + 3 ^ 40 * 149569 * 2
def baseEnd_149569 : Nat := 5056842009048924727549

theorem tailTrace_149569 : CollatzResearch.WordTrace tailWord_149569 prefixEnd_149569 5056842009048924727549 := by
  unfold tailWord_149569
  simp only [CollatzResearch.WordTrace]
  refine ⟨5455229595144532196619761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3636819730096354797746507 5455229595144532196619761)
  ·
    refine ⟨4091422196358399147464821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5455229595144532196619761 4091422196358399147464821)
    ·
      refine ⟨383570830908599920074827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4091422196358399147464821 383570830908599920074827)
      ·
        refine ⟨575356246362899880112241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383570830908599920074827 575356246362899880112241)
        ·
          refine ⟨431517184772174910084181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 575356246362899880112241 431517184772174910084181)
          ·
            refine ⟨5056842009048924727549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 431517184772174910084181 5056842009048924727549)
            ·
              rfl

theorem cell19_149569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 8].length) (baseStart_149569 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_149569 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_149569 prefixEnd_149569 := by exact prefixLift 149569
  have htrace : WordTrace (prefixWord ++ tailWord_149569) baseStart_149569 baseEnd_149569 := by
    simpa [prefixWord, tailWord_149569, baseEnd_149569] using wordTrace_append hprefix tailTrace_149569
  have hstable : (prefixWord ++ tailWord_149569).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149569).length < 2 ^ (prefixWord ++ tailWord_149569).sum := by decide
  have hdescent : baseEnd_149569 < baseStart_149569 := by decide
  rcases family_descends (prefixWord ++ tailWord_149569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149605 : List Nat := [1, 3, 1, 3, 2, 3, 3, 3]
def baseStart_149605 : Nat := 118140960795 + 149605 * 2 ^ 59
def prefixEnd_149605 : Nat := 4983230072969 + 3 ^ 40 * 149605 * 2
def baseEnd_149605 : Nat := 45522532335402905747843

theorem tailTrace_149605 : CollatzResearch.WordTrace tailWord_149605 prefixEnd_149605 45522532335402905747843 := by
  unfold tailWord_149605
  simp only [CollatzResearch.WordTrace]
  refine ⟨5456542623014110344930269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3637695082009406896620179 5456542623014110344930269)
  ·
    refine ⟨2046203483630291379348851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5456542623014110344930269 2046203483630291379348851)
    ·
      refine ⟨3069305225445437069023277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2046203483630291379348851 3069305225445437069023277)
      ·
        refine ⟨1150989459542038900883729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3069305225445437069023277 1150989459542038900883729)
        ·
          refine ⟨863242094656529175662797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1150989459542038900883729 863242094656529175662797)
          ·
            refine ⟨323715785496198440873549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 863242094656529175662797 323715785496198440873549)
            ·
              refine ⟨121393419561074415327581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 323715785496198440873549 121393419561074415327581)
              ·
                refine ⟨45522532335402905747843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121393419561074415327581 45522532335402905747843)
                ·
                  rfl

theorem cell19_149605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 3].length) (baseStart_149605 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_149605 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_149605 prefixEnd_149605 := by exact prefixLift 149605
  have htrace : WordTrace (prefixWord ++ tailWord_149605) baseStart_149605 baseEnd_149605 := by
    simpa [prefixWord, tailWord_149605, baseEnd_149605] using wordTrace_append hprefix tailTrace_149605
  have hstable : (prefixWord ++ tailWord_149605).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149605).length < 2 ^ (prefixWord ++ tailWord_149605).sum := by decide
  have hdescent : baseEnd_149605 < baseStart_149605 := by decide
  rcases family_descends (prefixWord ++ tailWord_149605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149658 : List Nat := [3, 1, 1, 5, 3, 1, 2, 3]
def baseStart_149658 : Nat := 118140960795 + 149658 * 2 ^ 59
def prefixEnd_149658 : Nat := 4983230072969 + 3 ^ 40 * 149658 * 2
def baseEnd_149658 : Nat := 45538659431514486569921

theorem tailTrace_149658 : CollatzResearch.WordTrace tailWord_149658 prefixEnd_149658 45538659431514486569921 := by
  unfold tailWord_149658
  simp only [CollatzResearch.WordTrace]
  refine ⟨1364618922955525099152407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3638983794548066931073085 1364618922955525099152407)
  ·
    refine ⟨2046928384433287648728611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1364618922955525099152407 2046928384433287648728611)
    ·
      refine ⟨3070392576649931473092917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2046928384433287648728611 3070392576649931473092917)
      ·
        refine ⟨287849304060931075602461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3070392576649931473092917 287849304060931075602461)
        ·
          refine ⟨107943489022849153350923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 287849304060931075602461 107943489022849153350923)
          ·
            refine ⟨161915233534273730026385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107943489022849153350923 161915233534273730026385)
            ·
              refine ⟨121436425150705297519789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161915233534273730026385 121436425150705297519789)
              ·
                refine ⟨45538659431514486569921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121436425150705297519789 45538659431514486569921)
                ·
                  rfl

theorem cell19_149658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_149658 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_149658 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_149658 prefixEnd_149658 := by exact prefixLift 149658
  have htrace : WordTrace (prefixWord ++ tailWord_149658) baseStart_149658 baseEnd_149658 := by
    simpa [prefixWord, tailWord_149658, baseEnd_149658] using wordTrace_append hprefix tailTrace_149658
  have hstable : (prefixWord ++ tailWord_149658).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149658).length < 2 ^ (prefixWord ++ tailWord_149658).sum := by decide
  have hdescent : baseEnd_149658 < baseStart_149658 := by decide
  rcases family_descends (prefixWord ++ tailWord_149658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149664 : List Nat := [2, 1, 1, 4, 2, 3, 1, 5]
def baseStart_149664 : Nat := 118140960795 + 149664 * 2 ^ 59
def prefixEnd_149664 : Nat := 4983230072969 + 3 ^ 40 * 149664 * 2
def baseEnd_149664 : Nat := 45540485140508250436571

theorem tailTrace_149664 : CollatzResearch.WordTrace tailWord_149664 prefixEnd_149664 45540485140508250436571 := by
  unfold tailWord_149664
  simp only [CollatzResearch.WordTrace]
  refine ⟨2729347264900181710664023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3639129686533575614218697 2729347264900181710664023)
  ·
    refine ⟨4094020897350272565996035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2729347264900181710664023 4094020897350272565996035)
    ·
      refine ⟨6141031346025408848994053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4094020897350272565996035 6141031346025408848994053)
      ·
        refine ⟨1151443377379764159186385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6141031346025408848994053 1151443377379764159186385)
        ·
          refine ⟨863582533034823119389789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1151443377379764159186385 863582533034823119389789)
          ·
            refine ⟨323843449888058669771171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 863582533034823119389789 323843449888058669771171)
            ·
              refine ⟨485765174832088004656757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323843449888058669771171 485765174832088004656757)
              ·
                refine ⟨45540485140508250436571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 485765174832088004656757 45540485140508250436571)
                ·
                  rfl

theorem cell19_149664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_149664 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_149664 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_149664 prefixEnd_149664 := by exact prefixLift 149664
  have htrace : WordTrace (prefixWord ++ tailWord_149664) baseStart_149664 baseEnd_149664 := by
    simpa [prefixWord, tailWord_149664, baseEnd_149664] using wordTrace_append hprefix tailTrace_149664
  have hstable : (prefixWord ++ tailWord_149664).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149664).length < 2 ^ (prefixWord ++ tailWord_149664).sum := by decide
  have hdescent : baseEnd_149664 < baseStart_149664 := by decide
  rcases family_descends (prefixWord ++ tailWord_149664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149681 : List Nat := [1, 2, 2, 5, 2, 2, 5]
def baseStart_149681 : Nat := 118140960795 + 149681 * 2 ^ 59
def prefixEnd_149681 : Nat := 4983230072969 + 3 ^ 40 * 149681 * 2
def baseEnd_149681 : Nat := 15181885994219082686249

theorem tailTrace_149681 : CollatzResearch.WordTrace tailWord_149681 prefixEnd_149681 15181885994219082686249 := by
  unfold tailWord_149681
  simp only [CollatzResearch.WordTrace]
  refine ⟨5459314570738775324696897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3639543047159183549797931 5459314570738775324696897)
  ·
    refine ⟨4094485928054081493522673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5459314570738775324696897 4094485928054081493522673)
    ·
      refine ⟨3070864446040561120142005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4094485928054081493522673 3070864446040561120142005)
      ·
        refine ⟨287893541816302605013313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3070864446040561120142005 287893541816302605013313)
        ·
          refine ⟨215920156362226953759985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287893541816302605013313 215920156362226953759985)
          ·
            refine ⟨161940117271670215319989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215920156362226953759985 161940117271670215319989)
            ·
              refine ⟨15181885994219082686249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 161940117271670215319989 15181885994219082686249)
              ·
                rfl

theorem cell19_149681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 5].length) (baseStart_149681 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_149681 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_149681 prefixEnd_149681 := by exact prefixLift 149681
  have htrace : WordTrace (prefixWord ++ tailWord_149681) baseStart_149681 baseEnd_149681 := by
    simpa [prefixWord, tailWord_149681, baseEnd_149681] using wordTrace_append hprefix tailTrace_149681
  have hstable : (prefixWord ++ tailWord_149681).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149681).length < 2 ^ (prefixWord ++ tailWord_149681).sum := by decide
  have hdescent : baseEnd_149681 < baseStart_149681 := by decide
  rcases family_descends (prefixWord ++ tailWord_149681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149698 : List Nat := [3, 5, 1, 1, 1, 1, 1, 6]
def baseStart_149698 : Nat := 118140960795 + 149698 * 2 ^ 59
def prefixEnd_149698 : Nat := 4983230072969 + 3 ^ 40 * 149698 * 2
def baseEnd_149698 : Nat := 45550830824806245680923

theorem tailTrace_149698 : CollatzResearch.WordTrace tailWord_149698 prefixEnd_149698 45550830824806245680923 := by
  unfold tailWord_149698
  simp only [CollatzResearch.WordTrace]
  refine ⟨1364983652919296807016437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3639956407784791485377165 1364983652919296807016437)
  ·
    refine ⟨127967217461184075657791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1364983652919296807016437 127967217461184075657791)
    ·
      refine ⟨191950826191776113486687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127967217461184075657791 191950826191776113486687)
      ·
        refine ⟨287926239287664170230031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191950826191776113486687 287926239287664170230031)
        ·
          refine ⟨431889358931496255345047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287926239287664170230031 431889358931496255345047)
          ·
            refine ⟨647834038397244383017571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431889358931496255345047 647834038397244383017571)
            ·
              refine ⟨971751057595866574526357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 647834038397244383017571 971751057595866574526357)
              ·
                refine ⟨45550830824806245680923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 971751057595866574526357 45550830824806245680923)
                ·
                  rfl

theorem cell19_149698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_149698 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_149698 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_149698 prefixEnd_149698 := by exact prefixLift 149698
  have htrace : WordTrace (prefixWord ++ tailWord_149698) baseStart_149698 baseEnd_149698 := by
    simpa [prefixWord, tailWord_149698, baseEnd_149698] using wordTrace_append hprefix tailTrace_149698
  have hstable : (prefixWord ++ tailWord_149698).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149698).length < 2 ^ (prefixWord ++ tailWord_149698).sum := by decide
  have hdescent : baseEnd_149698 < baseStart_149698 := by decide
  rcases family_descends (prefixWord ++ tailWord_149698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149700 : List Nat := [2, 3, 3, 1, 2, 2, 2, 4]
def baseStart_149700 : Nat := 118140960795 + 149700 * 2 ^ 59
def prefixEnd_149700 : Nat := 4983230072969 + 3 ^ 40 * 149700 * 2
def baseEnd_149700 : Nat := 45551439394470833636473

theorem tailTrace_149700 : CollatzResearch.WordTrace tailWord_149700 prefixEnd_149700 45551439394470833636473 := by
  unfold tailWord_149700
  simp only [CollatzResearch.WordTrace]
  refine ⟨2730003778834970784819277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3640005038446627713092369 2730003778834970784819277)
  ·
    refine ⟨1023751417063114044307229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2730003778834970784819277 1023751417063114044307229)
    ·
      refine ⟨383906781398667766615211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1023751417063114044307229 383906781398667766615211)
      ·
        refine ⟨575860172098001649922817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383906781398667766615211 575860172098001649922817)
        ·
          refine ⟨431895129073501237442113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 575860172098001649922817 431895129073501237442113)
          ·
            refine ⟨323921346805125928081585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 431895129073501237442113 323921346805125928081585)
            ·
              refine ⟨242941010103844446061189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 323921346805125928081585 242941010103844446061189)
              ·
                refine ⟨45551439394470833636473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 242941010103844446061189 45551439394470833636473)
                ·
                  rfl

theorem cell19_149700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_149700 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_149700 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_149700 prefixEnd_149700 := by exact prefixLift 149700
  have htrace : WordTrace (prefixWord ++ tailWord_149700) baseStart_149700 baseEnd_149700 := by
    simpa [prefixWord, tailWord_149700, baseEnd_149700] using wordTrace_append hprefix tailTrace_149700
  have hstable : (prefixWord ++ tailWord_149700).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149700).length < 2 ^ (prefixWord ++ tailWord_149700).sum := by decide
  have hdescent : baseEnd_149700 < baseStart_149700 := by decide
  rcases family_descends (prefixWord ++ tailWord_149700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149797 : List Nat := [1, 3, 1, 2, 5, 1, 6]
def baseStart_149797 : Nat := 118140960795 + 149797 * 2 ^ 59
def prefixEnd_149797 : Nat := 4983230072969 + 3 ^ 40 * 149797 * 2
def baseEnd_149797 : Nat := 15193651674401116493551

theorem tailTrace_149797 : CollatzResearch.WordTrace tailWord_149797 prefixEnd_149797 15193651674401116493551 := by
  unfold tailWord_149797
  simp only [CollatzResearch.WordTrace]
  refine ⟨5463545438318527135919645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3642363625545684757279763 5463545438318527135919645)
  ·
    refine ⟨2048829539369447675969867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5463545438318527135919645 2048829539369447675969867)
    ·
      refine ⟨3073244309054171513954801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2048829539369447675969867 3073244309054171513954801)
      ·
        refine ⟨2304933231790628635466101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3073244309054171513954801 2304933231790628635466101)
        ·
          refine ⟨216087490480371434574947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2304933231790628635466101 216087490480371434574947)
          ·
            refine ⟨324131235720557151862421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216087490480371434574947 324131235720557151862421)
            ·
              refine ⟨15193651674401116493551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 324131235720557151862421 15193651674401116493551)
              ·
                rfl

theorem cell19_149797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 6].length) (baseStart_149797 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_149797 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_149797 prefixEnd_149797 := by exact prefixLift 149797
  have htrace : WordTrace (prefixWord ++ tailWord_149797) baseStart_149797 baseEnd_149797 := by
    simpa [prefixWord, tailWord_149797, baseEnd_149797] using wordTrace_append hprefix tailTrace_149797
  have hstable : (prefixWord ++ tailWord_149797).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149797).length < 2 ^ (prefixWord ++ tailWord_149797).sum := by decide
  have hdescent : baseEnd_149797 < baseStart_149797 := by decide
  rcases family_descends (prefixWord ++ tailWord_149797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149928 : List Nat := [2, 1, 6, 1, 1, 1, 3, 4]
def baseStart_149928 : Nat := 118140960795 + 149928 * 2 ^ 59
def prefixEnd_149928 : Nat := 4983230072969 + 3 ^ 40 * 149928 * 2
def baseEnd_149928 : Nat := 45620816336233860569185

theorem tailTrace_149928 : CollatzResearch.WordTrace tailWord_149928 prefixEnd_149928 45620816336233860569185 := by
  unfold tailWord_149928
  simp only [CollatzResearch.WordTrace]
  refine ⟨2734161700421968254469219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3645548933895957672625625 2734161700421968254469219)
  ·
    refine ⟨4101242550632952381703829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2734161700421968254469219 4101242550632952381703829)
    ·
      refine ⟨192245744560919642892367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4101242550632952381703829 192245744560919642892367)
      ·
        refine ⟨288368616841379464338551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192245744560919642892367 288368616841379464338551)
        ·
          refine ⟨432552925262069196507827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288368616841379464338551 432552925262069196507827)
          ·
            refine ⟨648829387893103794761741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432552925262069196507827 648829387893103794761741)
            ·
              refine ⟨243311020459913923035653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 648829387893103794761741 243311020459913923035653)
              ·
                refine ⟨45620816336233860569185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 243311020459913923035653 45620816336233860569185)
                ·
                  rfl

theorem cell19_149928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 4].length) (baseStart_149928 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_149928 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_149928 prefixEnd_149928 := by exact prefixLift 149928
  have htrace : WordTrace (prefixWord ++ tailWord_149928) baseStart_149928 baseEnd_149928 := by
    simpa [prefixWord, tailWord_149928, baseEnd_149928] using wordTrace_append hprefix tailTrace_149928
  have hstable : (prefixWord ++ tailWord_149928).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149928).length < 2 ^ (prefixWord ++ tailWord_149928).sum := by decide
  have hdescent : baseEnd_149928 < baseStart_149928 := by decide
  rcases family_descends (prefixWord ++ tailWord_149928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150002 : List Nat := [3, 2, 1, 4, 2, 2, 2, 3]
def baseStart_150002 : Nat := 118140960795 + 150002 * 2 ^ 59
def prefixEnd_150002 : Nat := 4983230072969 + 3 ^ 40 * 150002 * 2
def baseEnd_150002 : Nat := 45643333413823614924539

theorem tailTrace_150002 : CollatzResearch.WordTrace tailWord_150002 prefixEnd_150002 45643333413823614924539 := by
  unfold tailWord_150002
  simp only [CollatzResearch.WordTrace]
  refine ⟨1367755600643961786783065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3647348268383898098088173 1367755600643961786783065)
  ·
    refine ⟨1025816700482971340087299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1367755600643961786783065 1025816700482971340087299)
    ·
      refine ⟨1538725050724457010130949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1025816700482971340087299 1538725050724457010130949)
      ·
        refine ⟨288510947010835689399553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1538725050724457010130949 288510947010835689399553)
        ·
          refine ⟨216383210258126767049665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288510947010835689399553 216383210258126767049665)
          ·
            refine ⟨162287407693595075287249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216383210258126767049665 162287407693595075287249)
            ·
              refine ⟨121715555770196306465437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162287407693595075287249 121715555770196306465437)
              ·
                refine ⟨45643333413823614924539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121715555770196306465437 45643333413823614924539)
                ·
                  rfl

theorem cell19_150002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_150002 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150002 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150002 prefixEnd_150002 := by exact prefixLift 150002
  have htrace : WordTrace (prefixWord ++ tailWord_150002) baseStart_150002 baseEnd_150002 := by
    simpa [prefixWord, tailWord_150002, baseEnd_150002] using wordTrace_append hprefix tailTrace_150002
  have hstable : (prefixWord ++ tailWord_150002).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150002).length < 2 ^ (prefixWord ++ tailWord_150002).sum := by decide
  have hdescent : baseEnd_150002 < baseStart_150002 := by decide
  rcases family_descends (prefixWord ++ tailWord_150002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150006 : List Nat := [5, 1, 1, 1, 2, 1, 3, 5]
def baseStart_150006 : Nat := 118140960795 + 150006 * 2 ^ 59
def prefixEnd_150006 : Nat := 4983230072969 + 3 ^ 40 * 150006 * 2
def baseEnd_150006 : Nat := 45644550553152790835639

theorem tailTrace_150006 : CollatzResearch.WordTrace tailWord_150006 prefixEnd_150006 45644550553152790835639 := by
  unfold tailWord_150006
  simp only [CollatzResearch.WordTrace]
  refine ⟨341948018410084739392367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3647445529707570553518581 341948018410084739392367)
  ·
    refine ⟨512922027615127109088551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 341948018410084739392367 512922027615127109088551)
    ·
      refine ⟨769383041422690663632827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 512922027615127109088551 769383041422690663632827)
      ·
        refine ⟨1154074562134035995449241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 769383041422690663632827 1154074562134035995449241)
        ·
          refine ⟨865555921600526996586931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1154074562134035995449241 865555921600526996586931)
          ·
            refine ⟨1298333882400790494880397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 865555921600526996586931 1298333882400790494880397)
            ·
              refine ⟨486875205900296435580149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1298333882400790494880397 486875205900296435580149)
              ·
                refine ⟨45644550553152790835639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 486875205900296435580149 45644550553152790835639)
                ·
                  rfl

theorem cell19_150006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_150006 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150006 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150006 prefixEnd_150006 := by exact prefixLift 150006
  have htrace : WordTrace (prefixWord ++ tailWord_150006) baseStart_150006 baseEnd_150006 := by
    simpa [prefixWord, tailWord_150006, baseEnd_150006] using wordTrace_append hprefix tailTrace_150006
  have hstable : (prefixWord ++ tailWord_150006).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150006).length < 2 ^ (prefixWord ++ tailWord_150006).sum := by decide
  have hdescent : baseEnd_150006 < baseStart_150006 := by decide
  rcases family_descends (prefixWord ++ tailWord_150006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150008 : List Nat := [2, 1, 2, 1, 1, 4, 3, 5]
def baseStart_150008 : Nat := 118140960795 + 150008 * 2 ^ 59
def prefixEnd_150008 : Nat := 4983230072969 + 3 ^ 40 * 150008 * 2
def baseEnd_150008 : Nat := 45645159122817378791189

theorem tailTrace_150008 : CollatzResearch.WordTrace tailWord_150008 prefixEnd_150008 45645159122817378791189 := by
  unfold tailWord_150008
  simp only [CollatzResearch.WordTrace]
  refine ⟨2735620620277055085925339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3647494160369406781233785 2735620620277055085925339)
  ·
    refine ⟨4103430930415582628888009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2735620620277055085925339 4103430930415582628888009)
    ·
      refine ⟨3077573197811686971666007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4103430930415582628888009 3077573197811686971666007)
      ·
        refine ⟨4616359796717530457499011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3077573197811686971666007 4616359796717530457499011)
        ·
          refine ⟨6924539695076295686248517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4616359796717530457499011 6924539695076295686248517)
          ·
            refine ⟨1298351192826805441171597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6924539695076295686248517 1298351192826805441171597)
            ·
              refine ⟨486881697310052040439349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1298351192826805441171597 486881697310052040439349)
              ·
                refine ⟨45645159122817378791189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 486881697310052040439349 45645159122817378791189)
                ·
                  rfl

theorem cell19_150008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_150008 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150008 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150008 prefixEnd_150008 := by exact prefixLift 150008
  have htrace : WordTrace (prefixWord ++ tailWord_150008) baseStart_150008 baseEnd_150008 := by
    simpa [prefixWord, tailWord_150008, baseEnd_150008] using wordTrace_append hprefix tailTrace_150008
  have hstable : (prefixWord ++ tailWord_150008).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150008).length < 2 ^ (prefixWord ++ tailWord_150008).sum := by decide
  have hdescent : baseEnd_150008 < baseStart_150008 := by decide
  rcases family_descends (prefixWord ++ tailWord_150008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150023 : List Nat := [1, 1, 4, 3, 4, 1, 5]
def baseStart_150023 : Nat := 118140960795 + 150023 * 2 ^ 59
def prefixEnd_150023 : Nat := 4983230072969 + 3 ^ 40 * 150023 * 2
def baseEnd_150023 : Nat := 15216574465100596152605

theorem tailTrace_150023 : CollatzResearch.WordTrace tailWord_150023 prefixEnd_150023 15216574465100596152605 := by
  unfold tailWord_150023
  simp only [CollatzResearch.WordTrace]
  refine ⟨5471788335499767733646723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3647858890333178489097815 5471788335499767733646723)
  ·
    refine ⟨8207682503249651600470085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5471788335499767733646723 8207682503249651600470085)
    ·
      refine ⟨1538940469359309675088141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8207682503249651600470085 1538940469359309675088141)
      ·
        refine ⟨577102676009741128158053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1538940469359309675088141 577102676009741128158053)
        ·
          refine ⟨108206751751826461529635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 577102676009741128158053 108206751751826461529635)
          ·
            refine ⟨162310127627739692294453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108206751751826461529635 162310127627739692294453)
            ·
              refine ⟨15216574465100596152605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 162310127627739692294453 15216574465100596152605)
              ·
                rfl

theorem cell19_150023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 5].length) (baseStart_150023 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150023 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150023 prefixEnd_150023 := by exact prefixLift 150023
  have htrace : WordTrace (prefixWord ++ tailWord_150023) baseStart_150023 baseEnd_150023 := by
    simpa [prefixWord, tailWord_150023, baseEnd_150023] using wordTrace_append hprefix tailTrace_150023
  have hstable : (prefixWord ++ tailWord_150023).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150023).length < 2 ^ (prefixWord ++ tailWord_150023).sum := by decide
  have hdescent : baseEnd_150023 < baseStart_150023 := by decide
  rcases family_descends (prefixWord ++ tailWord_150023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150027 : List Nat := [1, 1, 1, 1, 7, 1, 7]
def baseStart_150027 : Nat := 118140960795 + 150027 * 2 ^ 59
def prefixEnd_150027 : Nat := 4983230072969 + 3 ^ 40 * 150027 * 2
def baseEnd_150027 : Nat := 15216980178210321456305

theorem tailTrace_150027 : CollatzResearch.WordTrace tailWord_150027 prefixEnd_150027 15216980178210321456305 := by
  unfold tailWord_150027
  simp only [CollatzResearch.WordTrace]
  refine ⟨5471934227485276416792335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3647956151656850944528223 5471934227485276416792335)
  ·
    refine ⟨8207901341227914625188503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5471934227485276416792335 8207901341227914625188503)
    ·
      refine ⟨12311852011841871937782755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8207901341227914625188503 12311852011841871937782755)
      ·
        refine ⟨18467778017762807906674133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12311852011841871937782755 18467778017762807906674133)
        ·
          refine ⟨432838547291315810312675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 18467778017762807906674133 432838547291315810312675)
          ·
            refine ⟨649257820936973715469013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432838547291315810312675 649257820936973715469013)
            ·
              refine ⟨15216980178210321456305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 649257820936973715469013 15216980178210321456305)
              ·
                rfl

theorem cell19_150027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 7].length) (baseStart_150027 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150027 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150027 prefixEnd_150027 := by exact prefixLift 150027
  have htrace : WordTrace (prefixWord ++ tailWord_150027) baseStart_150027 baseEnd_150027 := by
    simpa [prefixWord, tailWord_150027, baseEnd_150027] using wordTrace_append hprefix tailTrace_150027
  have hstable : (prefixWord ++ tailWord_150027).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150027).length < 2 ^ (prefixWord ++ tailWord_150027).sum := by decide
  have hdescent : baseEnd_150027 < baseStart_150027 := by decide
  rcases family_descends (prefixWord ++ tailWord_150027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150044 : List Nat := [2, 2, 3, 1, 2, 3, 2, 4]
def baseStart_150044 : Nat := 118140960795 + 150044 * 2 ^ 59
def prefixEnd_150044 : Nat := 4983230072969 + 3 ^ 40 * 150044 * 2
def baseEnd_150044 : Nat := 45656113376779961991091

theorem tailTrace_150044 : CollatzResearch.WordTrace tailWord_150044 prefixEnd_150044 45656113376779961991091 := by
  unfold tailWord_150044
  simp only [CollatzResearch.WordTrace]
  refine ⟨2736277134211844160080593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3648369512282458880107457 2736277134211844160080593)
  ·
    refine ⟨2052207850658883120060445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2736277134211844160080593 2052207850658883120060445)
    ·
      refine ⟨769577943997081170022667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2052207850658883120060445 769577943997081170022667)
      ·
        refine ⟨1154366915995621755034001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 769577943997081170022667 1154366915995621755034001)
        ·
          refine ⟨865775186996716316275501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1154366915995621755034001 865775186996716316275501)
          ·
            refine ⟨324665695123768618603313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 865775186996716316275501 324665695123768618603313)
            ·
              refine ⟨243499271342826463952485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 324665695123768618603313 243499271342826463952485)
              ·
                refine ⟨45656113376779961991091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 243499271342826463952485 45656113376779961991091)
                ·
                  rfl

theorem cell19_150044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_150044 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150044 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150044 prefixEnd_150044 := by exact prefixLift 150044
  have htrace : WordTrace (prefixWord ++ tailWord_150044) baseStart_150044 baseEnd_150044 := by
    simpa [prefixWord, tailWord_150044, baseEnd_150044] using wordTrace_append hprefix tailTrace_150044
  have hstable : (prefixWord ++ tailWord_150044).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150044).length < 2 ^ (prefixWord ++ tailWord_150044).sum := by decide
  have hdescent : baseEnd_150044 < baseStart_150044 := by decide
  rcases family_descends (prefixWord ++ tailWord_150044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150065 : List Nat := [1, 2, 2, 3, 1, 1, 4, 5]
def baseStart_150065 : Nat := 118140960795 + 150065 * 2 ^ 59
def prefixEnd_150065 : Nat := 4983230072969 + 3 ^ 40 * 150065 * 2
def baseEnd_150065 : Nat := 45662503358258135524367

theorem tailTrace_150065 : CollatzResearch.WordTrace tailWord_150065 prefixEnd_150065 45662503358258135524367 := by
  unfold tailWord_150065
  simp only [CollatzResearch.WordTrace]
  refine ⟨5473320201347608906675649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3648880134231739271117099 5473320201347608906675649)
  ·
    refine ⟨4104990151010706680006737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5473320201347608906675649 4104990151010706680006737)
    ·
      refine ⟨3078742613258030010005053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4104990151010706680006737 3078742613258030010005053)
      ·
        refine ⟨1154528479971761253751895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3078742613258030010005053 1154528479971761253751895)
        ·
          refine ⟨1731792719957641880627843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1154528479971761253751895 1731792719957641880627843)
          ·
            refine ⟨2597689079936462820941765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1731792719957641880627843 2597689079936462820941765)
            ·
              refine ⟨487066702488086778926581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2597689079936462820941765 487066702488086778926581)
              ·
                refine ⟨45662503358258135524367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 487066702488086778926581 45662503358258135524367)
                ·
                  rfl

theorem cell19_150065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 5].length) (baseStart_150065 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150065 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150065 prefixEnd_150065 := by exact prefixLift 150065
  have htrace : WordTrace (prefixWord ++ tailWord_150065) baseStart_150065 baseEnd_150065 := by
    simpa [prefixWord, tailWord_150065, baseEnd_150065] using wordTrace_append hprefix tailTrace_150065
  have hstable : (prefixWord ++ tailWord_150065).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150065).length < 2 ^ (prefixWord ++ tailWord_150065).sum := by decide
  have hdescent : baseEnd_150065 < baseStart_150065 := by decide
  rcases family_descends (prefixWord ++ tailWord_150065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150177 : List Nat := [1, 2, 3, 3, 3, 1, 1, 5]
def baseStart_150177 : Nat := 118140960795 + 150177 * 2 ^ 59
def prefixEnd_150177 : Nat := 4983230072969 + 3 ^ 40 * 150177 * 2
def baseEnd_150177 : Nat := 45696583259475061035173

theorem tailTrace_150177 : CollatzResearch.WordTrace tailWord_150177 prefixEnd_150177 45696583259475061035173 := by
  unfold tailWord_150177
  simp only [CollatzResearch.WordTrace]
  refine ⟨5477405176941852034752785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3651603451294568023168523 5477405176941852034752785)
  ·
    refine ⟨4108053882706389026064589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5477405176941852034752785 4108053882706389026064589)
    ·
      refine ⟨1540520206014895884774221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4108053882706389026064589 1540520206014895884774221)
      ·
        refine ⟨577695077255585956790333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1540520206014895884774221 577695077255585956790333)
        ·
          refine ⟨216635653970844733796375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 577695077255585956790333 216635653970844733796375)
          ·
            refine ⟨324953480956267100694563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216635653970844733796375 324953480956267100694563)
            ·
              refine ⟨487430221434400651041845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 324953480956267100694563 487430221434400651041845)
              ·
                refine ⟨45696583259475061035173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 487430221434400651041845 45696583259475061035173)
                ·
                  rfl

theorem cell19_150177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 5].length) (baseStart_150177 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150177 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150177 prefixEnd_150177 := by exact prefixLift 150177
  have htrace : WordTrace (prefixWord ++ tailWord_150177) baseStart_150177 baseEnd_150177 := by
    simpa [prefixWord, tailWord_150177, baseEnd_150177] using wordTrace_append hprefix tailTrace_150177
  have hstable : (prefixWord ++ tailWord_150177).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150177).length < 2 ^ (prefixWord ++ tailWord_150177).sum := by decide
  have hdescent : baseEnd_150177 < baseStart_150177 := by decide
  rcases family_descends (prefixWord ++ tailWord_150177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150270 : List Nat := [4, 2, 2, 1, 2, 3, 1, 4]
def baseStart_150270 : Nat := 118140960795 + 150270 * 2 ^ 59
def prefixEnd_150270 : Nat := 4983230072969 + 3 ^ 40 * 150270 * 2
def baseEnd_150270 : Nat := 45724881748878400968253

theorem tailTrace_150270 : CollatzResearch.WordTrace tailWord_150270 prefixEnd_150270 45724881748878400968253 := by
  unfold tailWord_150270
  simp only [CollatzResearch.WordTrace]
  refine ⟨685099645700616114736033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3653864777069952611925509 685099645700616114736033)
  ·
    refine ⟨513824734275462086052025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 685099645700616114736033 513824734275462086052025)
    ·
      refine ⟨385368550706596564539019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 513824734275462086052025 385368550706596564539019)
      ·
        refine ⟨578052826059894846808529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385368550706596564539019 578052826059894846808529)
        ·
          refine ⟨433539619544921135106397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 578052826059894846808529 433539619544921135106397)
          ·
            refine ⟨162577357329345425664899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 433539619544921135106397 162577357329345425664899)
            ·
              refine ⟨243866035994018138497349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162577357329345425664899 243866035994018138497349)
              ·
                refine ⟨45724881748878400968253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 243866035994018138497349 45724881748878400968253)
                ·
                  rfl

theorem cell19_150270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_150270 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150270 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150270 prefixEnd_150270 := by exact prefixLift 150270
  have htrace : WordTrace (prefixWord ++ tailWord_150270) baseStart_150270 baseEnd_150270 := by
    simpa [prefixWord, tailWord_150270, baseEnd_150270] using wordTrace_append hprefix tailTrace_150270
  have hstable : (prefixWord ++ tailWord_150270).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150270).length < 2 ^ (prefixWord ++ tailWord_150270).sum := by decide
  have hdescent : baseEnd_150270 < baseStart_150270 := by decide
  rcases family_descends (prefixWord ++ tailWord_150270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150312 : List Nat := [2, 1, 5, 1, 1, 1, 8]
def baseStart_150312 : Nat := 118140960795 + 150312 * 2 ^ 59
def prefixEnd_150312 : Nat := 4983230072969 + 3 ^ 40 * 150312 * 2
def baseEnd_150312 : Nat := 15245887237278249344935

theorem tailTrace_150312 : CollatzResearch.WordTrace tailWord_150312 prefixEnd_150312 15245887237278249344935 := by
  unfold tailWord_150312
  simp only [CollatzResearch.WordTrace]
  refine ⟨2741164515726385045458595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3654886020968513393944793 2741164515726385045458595)
  ·
    refine ⟨4111746773589577568187893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2741164515726385045458595 4111746773589577568187893)
    ·
      refine ⟨385476260024022897017615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4111746773589577568187893 385476260024022897017615)
      ·
        refine ⟨578214390036034345526423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385476260024022897017615 578214390036034345526423)
        ·
          refine ⟨867321585054051518289635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 578214390036034345526423 867321585054051518289635)
          ·
            refine ⟨1300982377581077277434453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 867321585054051518289635 1300982377581077277434453)
            ·
              refine ⟨15245887237278249344935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1300982377581077277434453 15245887237278249344935)
              ·
                rfl

theorem cell19_150312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 8].length) (baseStart_150312 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150312 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150312 prefixEnd_150312 := by exact prefixLift 150312
  have htrace : WordTrace (prefixWord ++ tailWord_150312) baseStart_150312 baseEnd_150312 := by
    simpa [prefixWord, tailWord_150312, baseEnd_150312] using wordTrace_append hprefix tailTrace_150312
  have hstable : (prefixWord ++ tailWord_150312).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150312).length < 2 ^ (prefixWord ++ tailWord_150312).sum := by decide
  have hdescent : baseEnd_150312 < baseStart_150312 := by decide
  rcases family_descends (prefixWord ++ tailWord_150312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150342 : List Nat := [6, 1, 1, 2, 2, 2, 2, 3]
def baseStart_150342 : Nat := 118140960795 + 150342 * 2 ^ 59
def prefixEnd_150342 : Nat := 4983230072969 + 3 ^ 40 * 150342 * 2
def baseEnd_150342 : Nat := 45746790256803567368057

theorem tailTrace_150342 : CollatzResearch.WordTrace tailWord_150342 prefixEnd_150342 45746790256803567368057 := by
  unfold tailWord_150342
  simp only [CollatzResearch.WordTrace]
  refine ⟨171356975667002662953415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3655615480896056809672853 171356975667002662953415)
  ·
    refine ⟨257035463500503994430123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171356975667002662953415 257035463500503994430123)
    ·
      refine ⟨385553195250755991645185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257035463500503994430123 385553195250755991645185)
      ·
        refine ⟨289164896438066993733889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 385553195250755991645185 289164896438066993733889)
        ·
          refine ⟨216873672328550245300417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289164896438066993733889 216873672328550245300417)
          ·
            refine ⟨162655254246412683975313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216873672328550245300417 162655254246412683975313)
            ·
              refine ⟨121991440684809512981485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162655254246412683975313 121991440684809512981485)
              ·
                refine ⟨45746790256803567368057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121991440684809512981485 45746790256803567368057)
                ·
                  rfl

theorem cell19_150342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_150342 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150342 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150342 prefixEnd_150342 := by exact prefixLift 150342
  have htrace : WordTrace (prefixWord ++ tailWord_150342) baseStart_150342 baseEnd_150342 := by
    simpa [prefixWord, tailWord_150342, baseEnd_150342] using wordTrace_append hprefix tailTrace_150342
  have hstable : (prefixWord ++ tailWord_150342).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150342).length < 2 ^ (prefixWord ++ tailWord_150342).sum := by decide
  have hdescent : baseEnd_150342 < baseStart_150342 := by decide
  rcases family_descends (prefixWord ++ tailWord_150342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150348 : List Nat := [2, 2, 1, 3, 3, 1, 4, 3]
def baseStart_150348 : Nat := 118140960795 + 150348 * 2 ^ 59
def prefixEnd_150348 : Nat := 4983230072969 + 3 ^ 40 * 150348 * 2
def baseEnd_150348 : Nat := 45748615965797331234707

theorem tailTrace_150348 : CollatzResearch.WordTrace tailWord_150348 prefixEnd_150348 45748615965797331234707 := by
  unfold tailWord_150348
  simp only [CollatzResearch.WordTrace]
  refine ⟨2741821029661174119613849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3655761372881565492818465 2741821029661174119613849)
  ·
    refine ⟨2056365772245880589710387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2741821029661174119613849 2056365772245880589710387)
    ·
      refine ⟨3084548658368820884565581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2056365772245880589710387 3084548658368820884565581)
      ·
        refine ⟨1156705746888307831712093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3084548658368820884565581 1156705746888307831712093)
        ·
          refine ⟨433764655083115436892035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1156705746888307831712093 433764655083115436892035)
          ·
            refine ⟨650646982624673155338053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433764655083115436892035 650646982624673155338053)
            ·
              refine ⟨121996309242126216625885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 650646982624673155338053 121996309242126216625885)
              ·
                refine ⟨45748615965797331234707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121996309242126216625885 45748615965797331234707)
                ·
                  rfl

theorem cell19_150348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 3].length) (baseStart_150348 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150348 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150348 prefixEnd_150348 := by exact prefixLift 150348
  have htrace : WordTrace (prefixWord ++ tailWord_150348) baseStart_150348 baseEnd_150348 := by
    simpa [prefixWord, tailWord_150348, baseEnd_150348] using wordTrace_append hprefix tailTrace_150348
  have hstable : (prefixWord ++ tailWord_150348).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150348).length < 2 ^ (prefixWord ++ tailWord_150348).sum := by decide
  have hdescent : baseEnd_150348 < baseStart_150348 := by decide
  rcases family_descends (prefixWord ++ tailWord_150348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150407 : List Nat := [1, 1, 4, 2, 3, 1, 2, 5]
def baseStart_150407 : Nat := 118140960795 + 150407 * 2 ^ 59
def prefixEnd_150407 : Nat := 4983230072969 + 3 ^ 40 * 150407 * 2
def baseEnd_150407 : Nat := 45766568770902675923435

theorem tailTrace_150407 : CollatzResearch.WordTrace tailWord_150407 prefixEnd_150407 45766568770902675923435 := by
  unfold tailWord_150407
  simp only [CollatzResearch.WordTrace]
  refine ⟨5485793966108601315625475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3657195977405734210416983 5485793966108601315625475)
  ·
    refine ⟨8228690949162901973438213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5485793966108601315625475 8228690949162901973438213)
    ·
      refine ⟨1542879552968044120019665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8228690949162901973438213 1542879552968044120019665)
      ·
        refine ⟨1157159664726033090014749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1542879552968044120019665 1157159664726033090014749)
        ·
          refine ⟨433934874272262408755531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1157159664726033090014749 433934874272262408755531)
          ·
            refine ⟨650902311408393613133297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433934874272262408755531 650902311408393613133297)
            ·
              refine ⟨488176733556295209849973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 650902311408393613133297 488176733556295209849973)
              ·
                refine ⟨45766568770902675923435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 488176733556295209849973 45766568770902675923435)
                ·
                  rfl

theorem cell19_150407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 5].length) (baseStart_150407 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150407 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150407 prefixEnd_150407 := by exact prefixLift 150407
  have htrace : WordTrace (prefixWord ++ tailWord_150407) baseStart_150407 baseEnd_150407 := by
    simpa [prefixWord, tailWord_150407, baseEnd_150407] using wordTrace_append hprefix tailTrace_150407
  have hstable : (prefixWord ++ tailWord_150407).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150407).length < 2 ^ (prefixWord ++ tailWord_150407).sum := by decide
  have hdescent : baseEnd_150407 < baseStart_150407 := by decide
  rcases family_descends (prefixWord ++ tailWord_150407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150422 : List Nat := [5, 3, 1, 1, 1, 8]
def baseStart_150422 : Nat := 118140960795 + 150422 * 2 ^ 59
def prefixEnd_150422 : Nat := 4983230072969 + 3 ^ 40 * 150422 * 2
def baseEnd_150422 : Nat := 5085681449265231732229

theorem tailTrace_150422 : CollatzResearch.WordTrace tailWord_150422 prefixEnd_150422 5085681449265231732229 := by
  unfold tailWord_150422
  simp only [CollatzResearch.WordTrace]
  refine ⟨342896316315891179838845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3657560707369505918281013 342896316315891179838845)
  ·
    refine ⟨128586118618459192439567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 342896316315891179838845 128586118618459192439567)
    ·
      refine ⟨192879177927688788659351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128586118618459192439567 192879177927688788659351)
      ·
        refine ⟨289318766891533182989027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192879177927688788659351 289318766891533182989027)
        ·
          refine ⟨433978150337299774483541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289318766891533182989027 433978150337299774483541)
          ·
            refine ⟨5085681449265231732229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 433978150337299774483541 5085681449265231732229)
            ·
              rfl

theorem cell19_150422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 8].length) (baseStart_150422 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150422 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150422 prefixEnd_150422 := by exact prefixLift 150422
  have htrace : WordTrace (prefixWord ++ tailWord_150422) baseStart_150422 baseEnd_150422 := by
    simpa [prefixWord, tailWord_150422, baseEnd_150422] using wordTrace_append hprefix tailTrace_150422
  have hstable : (prefixWord ++ tailWord_150422).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150422).length < 2 ^ (prefixWord ++ tailWord_150422).sum := by decide
  have hdescent : baseEnd_150422 < baseStart_150422 := by decide
  rcases family_descends (prefixWord ++ tailWord_150422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150426 : List Nat := [3, 1, 1, 4, 3, 7]
def baseStart_150426 : Nat := 118140960795 + 150426 * 2 ^ 59
def prefixEnd_150426 : Nat := 4983230072969 + 3 ^ 40 * 150426 * 2
def baseEnd_150426 : Nat := 5085816686968473500129

theorem tailTrace_150426 : CollatzResearch.WordTrace tailWord_150426 prefixEnd_150426 5085816686968473500129 := by
  unfold tailWord_150426
  simp only [CollatzResearch.WordTrace]
  refine ⟨1371621738259941890141783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3657657968693178373711421 1371621738259941890141783)
  ·
    refine ⟨2057432607389912835212675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1371621738259941890141783 2057432607389912835212675)
    ·
      refine ⟨3086148911084869252819013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2057432607389912835212675 3086148911084869252819013)
      ·
        refine ⟨578652920828412984903565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3086148911084869252819013 578652920828412984903565)
        ·
          refine ⟨216994845310654869338837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 578652920828412984903565 216994845310654869338837)
          ·
            refine ⟨5085816686968473500129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 216994845310654869338837 5085816686968473500129)
            ·
              rfl

theorem cell19_150426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 7].length) (baseStart_150426 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150426 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150426 prefixEnd_150426 := by exact prefixLift 150426
  have htrace : WordTrace (prefixWord ++ tailWord_150426) baseStart_150426 baseEnd_150426 := by
    simpa [prefixWord, tailWord_150426, baseEnd_150426] using wordTrace_append hprefix tailTrace_150426
  have hstable : (prefixWord ++ tailWord_150426).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150426).length < 2 ^ (prefixWord ++ tailWord_150426).sum := by decide
  have hdescent : baseEnd_150426 < baseStart_150426 := by decide
  rcases family_descends (prefixWord ++ tailWord_150426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150447 : List Nat := [1, 1, 2, 1, 2, 2, 2, 8]
def baseStart_150447 : Nat := 118140960795 + 150447 * 2 ^ 59
def prefixEnd_150447 : Nat := 4983230072969 + 3 ^ 40 * 150447 * 2
def baseEnd_150447 : Nat := 45778740164194435034437

theorem tailTrace_150447 : CollatzResearch.WordTrace tailWord_150447 prefixEnd_150447 45778740164194435034437 := by
  unfold tailWord_150447
  simp only [CollatzResearch.WordTrace]
  refine ⟨5487252885963688147081595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3658168590642458764721063 5487252885963688147081595)
  ·
    refine ⟨8230879328945532220622393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5487252885963688147081595 8230879328945532220622393)
    ·
      refine ⟨6173159496709149165466795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8230879328945532220622393 6173159496709149165466795)
      ·
        refine ⟨9259739245063723748200193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6173159496709149165466795 9259739245063723748200193)
        ·
          refine ⟨6944804433797792811150145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9259739245063723748200193 6944804433797792811150145)
          ·
            refine ⟨5208603325348344608362609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6944804433797792811150145 5208603325348344608362609)
            ·
              refine ⟨3906452494011258456271957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5208603325348344608362609 3906452494011258456271957)
              ·
                refine ⟨45778740164194435034437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3906452494011258456271957 45778740164194435034437)
                ·
                  rfl

theorem cell19_150447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 8].length) (baseStart_150447 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150447 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150447 prefixEnd_150447 := by exact prefixLift 150447
  have htrace : WordTrace (prefixWord ++ tailWord_150447) baseStart_150447 baseEnd_150447 := by
    simpa [prefixWord, tailWord_150447, baseEnd_150447] using wordTrace_append hprefix tailTrace_150447
  have hstable : (prefixWord ++ tailWord_150447).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150447).length < 2 ^ (prefixWord ++ tailWord_150447).sum := by decide
  have hdescent : baseEnd_150447 < baseStart_150447 := by decide
  rcases family_descends (prefixWord ++ tailWord_150447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150462 : List Nat := [4, 2, 1, 1, 1, 2, 5, 3]
def baseStart_150462 : Nat := 118140960795 + 150462 * 2 ^ 59
def prefixEnd_150462 : Nat := 4983230072969 + 3 ^ 40 * 150462 * 2
def baseEnd_150462 : Nat := 45783304436678844701063

theorem tailTrace_150462 : CollatzResearch.WordTrace tailWord_150462 prefixEnd_150462 45783304436678844701063 := by
  unfold tailWord_150462
  simp only [CollatzResearch.WordTrace]
  refine ⟨685974997613668213609705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3658533320606230472585093 685974997613668213609705)
  ·
    refine ⟨514481248210251160207279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 685974997613668213609705 514481248210251160207279)
    ·
      refine ⟨771721872315376740310919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 514481248210251160207279 771721872315376740310919)
      ·
        refine ⟨1157582808473065110466379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 771721872315376740310919 1157582808473065110466379)
        ·
          refine ⟨1736374212709597665699569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1157582808473065110466379 1736374212709597665699569)
          ·
            refine ⟨1302280659532198249274677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1736374212709597665699569 1302280659532198249274677)
            ·
              refine ⟨122088811831143585869501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1302280659532198249274677 122088811831143585869501)
              ·
                refine ⟨45783304436678844701063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122088811831143585869501 45783304436678844701063)
                ·
                  rfl

theorem cell19_150462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_150462 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150462 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150462 prefixEnd_150462 := by exact prefixLift 150462
  have htrace : WordTrace (prefixWord ++ tailWord_150462) baseStart_150462 baseEnd_150462 := by
    simpa [prefixWord, tailWord_150462, baseEnd_150462] using wordTrace_append hprefix tailTrace_150462
  have hstable : (prefixWord ++ tailWord_150462).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150462).length < 2 ^ (prefixWord ++ tailWord_150462).sum := by decide
  have hdescent : baseEnd_150462 < baseStart_150462 := by decide
  rcases family_descends (prefixWord ++ tailWord_150462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150477 : List Nat := [1, 6, 3, 1, 1, 1, 6]
def baseStart_150477 : Nat := 118140960795 + 150477 * 2 ^ 59
def prefixEnd_150477 : Nat := 4983230072969 + 3 ^ 40 * 150477 * 2
def baseEnd_150477 : Nat := 15262622903054418122563

theorem tailTrace_150477 : CollatzResearch.WordTrace tailWord_150477 prefixEnd_150477 15262622903054418122563 := by
  unfold tailWord_150477
  simp only [CollatzResearch.WordTrace]
  refine ⟨5488347075855003270673685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3658898050570002180449123 5488347075855003270673685)
  ·
    refine ⟨257266269180703278312829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5488347075855003270673685 257266269180703278312829)
    ·
      refine ⟨96474850942763729367311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257266269180703278312829 96474850942763729367311)
      ·
        refine ⟨144712276414145594050967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96474850942763729367311 144712276414145594050967)
        ·
          refine ⟨217068414621218391076451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144712276414145594050967 217068414621218391076451)
          ·
            refine ⟨325602621931827586614677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217068414621218391076451 325602621931827586614677)
            ·
              refine ⟨15262622903054418122563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 325602621931827586614677 15262622903054418122563)
              ·
                rfl

theorem cell19_150477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 6].length) (baseStart_150477 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150477 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150477 prefixEnd_150477 := by exact prefixLift 150477
  have htrace : WordTrace (prefixWord ++ tailWord_150477) baseStart_150477 baseEnd_150477 := by
    simpa [prefixWord, tailWord_150477, baseEnd_150477] using wordTrace_append hprefix tailTrace_150477
  have hstable : (prefixWord ++ tailWord_150477).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150477).length < 2 ^ (prefixWord ++ tailWord_150477).sum := by decide
  have hdescent : baseEnd_150477 < baseStart_150477 := by decide
  rcases family_descends (prefixWord ++ tailWord_150477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150517 : List Nat := [1, 3, 5, 2, 1, 1, 1, 5]
def baseStart_150517 : Nat := 118140960795 + 150517 * 2 ^ 59
def prefixEnd_150517 : Nat := 4983230072969 + 3 ^ 40 * 150517 * 2
def baseEnd_150517 : Nat := 45800040102455013478691

theorem tailTrace_150517 : CollatzResearch.WordTrace tailWord_150517 prefixEnd_150517 45800040102455013478691 := by
  unfold tailWord_150517
  simp only [CollatzResearch.WordTrace]
  refine ⟨5489805995710090102129805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3659870663806726734753203 5489805995710090102129805)
  ·
    refine ⟨2058677248391283788298677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5489805995710090102129805 2058677248391283788298677)
    ·
      refine ⟨193000992036682855153001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2058677248391283788298677 193000992036682855153001)
      ·
        refine ⟨144750744027512141364751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193000992036682855153001 144750744027512141364751)
        ·
          refine ⟨217126116041268212047127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144750744027512141364751 217126116041268212047127)
          ·
            refine ⟨325689174061902318070691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217126116041268212047127 325689174061902318070691)
            ·
              refine ⟨488533761092853477106037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 325689174061902318070691 488533761092853477106037)
              ·
                refine ⟨45800040102455013478691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 488533761092853477106037 45800040102455013478691)
                ·
                  rfl

theorem cell19_150517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 5].length) (baseStart_150517 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150517 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150517 prefixEnd_150517 := by exact prefixLift 150517
  have htrace : WordTrace (prefixWord ++ tailWord_150517) baseStart_150517 baseEnd_150517 := by
    simpa [prefixWord, tailWord_150517, baseEnd_150517] using wordTrace_append hprefix tailTrace_150517
  have hstable : (prefixWord ++ tailWord_150517).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150517).length < 2 ^ (prefixWord ++ tailWord_150517).sum := by decide
  have hdescent : baseEnd_150517 < baseStart_150517 := by decide
  rcases family_descends (prefixWord ++ tailWord_150517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150540 : List Nat := [2, 2, 1, 2, 3, 4, 5]
def baseStart_150540 : Nat := 118140960795 + 150540 * 2 ^ 59
def prefixEnd_150540 : Nat := 4983230072969 + 3 ^ 40 * 150540 * 2
def baseEnd_150540 : Nat := 15269012884532591655839

theorem tailTrace_150540 : CollatzResearch.WordTrace tailWord_150540 prefixEnd_150540 15269012884532591655839 := by
  unfold tailWord_150540
  simp only [CollatzResearch.WordTrace]
  refine ⟨2745322437313382515108537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3660429916417843353478049 2745322437313382515108537)
  ·
    refine ⟨2058991827985036886331403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2745322437313382515108537 2058991827985036886331403)
    ·
      refine ⟨3088487741977555329497105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2058991827985036886331403 3088487741977555329497105)
      ·
        refine ⟨2316365806483166497122829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3088487741977555329497105 2316365806483166497122829)
        ·
          refine ⟨868637177431187436421061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2316365806483166497122829 868637177431187436421061)
          ·
            refine ⟨162869470768347644328949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 868637177431187436421061 162869470768347644328949)
            ·
              refine ⟨15269012884532591655839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 162869470768347644328949 15269012884532591655839)
              ·
                rfl

theorem cell19_150540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 5].length) (baseStart_150540 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150540 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150540 prefixEnd_150540 := by exact prefixLift 150540
  have htrace : WordTrace (prefixWord ++ tailWord_150540) baseStart_150540 baseEnd_150540 := by
    simpa [prefixWord, tailWord_150540, baseEnd_150540] using wordTrace_append hprefix tailTrace_150540
  have hstable : (prefixWord ++ tailWord_150540).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150540).length < 2 ^ (prefixWord ++ tailWord_150540).sum := by decide
  have hdescent : baseEnd_150540 < baseStart_150540 := by decide
  rcases family_descends (prefixWord ++ tailWord_150540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150557 : List Nat := [1, 4, 2, 2, 3, 1, 2, 4]
def baseStart_150557 : Nat := 118140960795 + 150557 * 2 ^ 59
def prefixEnd_150557 : Nat := 4983230072969 + 3 ^ 40 * 150557 * 2
def baseEnd_150557 : Nat := 45812211495746772589693

theorem tailTrace_150557 : CollatzResearch.WordTrace tailWord_150557 prefixEnd_150557 45812211495746772589693 := by
  unfold tailWord_150557
  simp only [CollatzResearch.WordTrace]
  refine ⟨5491264915565176933585925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3660843277043451289057283 5491264915565176933585925)
  ·
    refine ⟨1029612171668470675047361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5491264915565176933585925 1029612171668470675047361)
    ·
      refine ⟨772209128751353006285521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1029612171668470675047361 772209128751353006285521)
      ·
        refine ⟨579156846563514754714141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 772209128751353006285521 579156846563514754714141)
        ·
          refine ⟨217183817461318033017803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 579156846563514754714141 217183817461318033017803)
          ·
            refine ⟨325775726191977049526705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217183817461318033017803 325775726191977049526705)
            ·
              refine ⟨244331794643982787145029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325775726191977049526705 244331794643982787145029)
              ·
                refine ⟨45812211495746772589693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 244331794643982787145029 45812211495746772589693)
                ·
                  rfl

theorem cell19_150557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 4].length) (baseStart_150557 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150557 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150557 prefixEnd_150557 := by exact prefixLift 150557
  have htrace : WordTrace (prefixWord ++ tailWord_150557) baseStart_150557 baseEnd_150557 := by
    simpa [prefixWord, tailWord_150557, baseEnd_150557] using wordTrace_append hprefix tailTrace_150557
  have hstable : (prefixWord ++ tailWord_150557).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150557).length < 2 ^ (prefixWord ++ tailWord_150557).sum := by decide
  have hdescent : baseEnd_150557 < baseStart_150557 := by decide
  rcases family_descends (prefixWord ++ tailWord_150557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150559 : List Nat := [1, 1, 2, 4, 1, 4, 2, 4]
def baseStart_150559 : Nat := 118140960795 + 150559 * 2 ^ 59
def prefixEnd_150559 : Nat := 4983230072969 + 3 ^ 40 * 150559 * 2
def baseEnd_150559 : Nat := 45812820065411360545243

theorem tailTrace_150559 : CollatzResearch.WordTrace tailWord_150559 prefixEnd_150559 45812820065411360545243 := by
  unfold tailWord_150559
  simp only [CollatzResearch.WordTrace]
  refine ⟨5491337861557931275158731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3660891907705287516772487 5491337861557931275158731)
  ·
    refine ⟨8237006792336896912738097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5491337861557931275158731 8237006792336896912738097)
    ·
      refine ⟨6177755094252672684553573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8237006792336896912738097 6177755094252672684553573)
      ·
        refine ⟨1158329080172376128353795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6177755094252672684553573 1158329080172376128353795)
        ·
          refine ⟨1737493620258564192530693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1158329080172376128353795 1737493620258564192530693)
          ·
            refine ⟨325780053798480786099505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1737493620258564192530693 325780053798480786099505)
            ·
              refine ⟨244335040348860589574629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325780053798480786099505 244335040348860589574629)
              ·
                refine ⟨45812820065411360545243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 244335040348860589574629 45812820065411360545243)
                ·
                  rfl

theorem cell19_150559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 4].length) (baseStart_150559 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150559 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150559 prefixEnd_150559 := by exact prefixLift 150559
  have htrace : WordTrace (prefixWord ++ tailWord_150559) baseStart_150559 baseEnd_150559 := by
    simpa [prefixWord, tailWord_150559, baseEnd_150559] using wordTrace_append hprefix tailTrace_150559
  have hstable : (prefixWord ++ tailWord_150559).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150559).length < 2 ^ (prefixWord ++ tailWord_150559).sum := by decide
  have hdescent : baseEnd_150559 < baseStart_150559 := by decide
  rcases family_descends (prefixWord ++ tailWord_150559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150599 : List Nat := [1, 1, 4, 1, 3, 9]
def baseStart_150599 : Nat := 118140960795 + 150599 * 2 ^ 59
def prefixEnd_150599 : Nat := 4983230072969 + 3 ^ 40 * 150599 * 2
def baseEnd_150599 : Nat := 5091665717633679961805

theorem tailTrace_150599 : CollatzResearch.WordTrace tailWord_150599 prefixEnd_150599 5091665717633679961805 := by
  unfold tailWord_150599
  simp only [CollatzResearch.WordTrace]
  refine ⟨5492796781413018106614851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3661864520942012071076567 5492796781413018106614851)
  ·
    refine ⟨8239195172119527159922277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5492796781413018106614851 8239195172119527159922277)
    ·
      refine ⟨1544849094772411342485427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8239195172119527159922277 1544849094772411342485427)
      ·
        refine ⟨2317273642158617013728141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1544849094772411342485427 2317273642158617013728141)
        ·
          refine ⟨868977615809481380148053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2317273642158617013728141 868977615809481380148053)
          ·
            refine ⟨5091665717633679961805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 868977615809481380148053 5091665717633679961805)
            ·
              rfl

theorem cell19_150599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 9].length) (baseStart_150599 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150599 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150599 prefixEnd_150599 := by exact prefixLift 150599
  have htrace : WordTrace (prefixWord ++ tailWord_150599) baseStart_150599 baseEnd_150599 := by
    simpa [prefixWord, tailWord_150599, baseEnd_150599] using wordTrace_append hprefix tailTrace_150599
  have hstable : (prefixWord ++ tailWord_150599).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150599).length < 2 ^ (prefixWord ++ tailWord_150599).sum := by decide
  have hdescent : baseEnd_150599 < baseStart_150599 := by decide
  rcases family_descends (prefixWord ++ tailWord_150599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150618 : List Nat := [3, 1, 1, 2, 1, 1, 2, 8]
def baseStart_150618 : Nat := 118140960795 + 150618 * 2 ^ 59
def prefixEnd_150618 : Nat := 4983230072969 + 3 ^ 40 * 150618 * 2
def baseEnd_150618 : Nat := 45830772870516705233971

theorem tailTrace_150618 : CollatzResearch.WordTrace tailWord_150618 prefixEnd_150618 45830772870516705233971 := by
  unfold tailWord_150618
  simp only [CollatzResearch.WordTrace]
  refine ⟨1373372442086046087889127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3662326512229456234371005 1373372442086046087889127)
  ·
    refine ⟨2060058663129069131833691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1373372442086046087889127 2060058663129069131833691)
    ·
      refine ⟨3090087994693603697750537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2060058663129069131833691 3090087994693603697750537)
      ·
        refine ⟨2317565996020202773312903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3090087994693603697750537 2317565996020202773312903)
        ·
          refine ⟨3476348994030304159969355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2317565996020202773312903 3476348994030304159969355)
          ·
            refine ⟨5214523491045456239954033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3476348994030304159969355 5214523491045456239954033)
            ·
              refine ⟨3910892618284092179965525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5214523491045456239954033 3910892618284092179965525)
              ·
                refine ⟨45830772870516705233971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3910892618284092179965525 45830772870516705233971)
                ·
                  rfl

theorem cell19_150618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_150618 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150618 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150618 prefixEnd_150618 := by exact prefixLift 150618
  have htrace : WordTrace (prefixWord ++ tailWord_150618) baseStart_150618 baseEnd_150618 := by
    simpa [prefixWord, tailWord_150618, baseEnd_150618] using wordTrace_append hprefix tailTrace_150618
  have hstable : (prefixWord ++ tailWord_150618).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150618).length < 2 ^ (prefixWord ++ tailWord_150618).sum := by decide
  have hdescent : baseEnd_150618 < baseStart_150618 := by decide
  rcases family_descends (prefixWord ++ tailWord_150618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150690 : List Nat := [3, 3, 1, 3, 2, 1, 1, 5]
def baseStart_150690 : Nat := 118140960795 + 150690 * 2 ^ 59
def prefixEnd_150690 : Nat := 4983230072969 + 3 ^ 40 * 150690 * 2
def baseEnd_150690 : Nat := 45852681378441871633775

theorem tailTrace_150690 : CollatzResearch.WordTrace tailWord_150690 prefixEnd_150690 45852681378441871633775 := by
  unfold tailWord_150690
  simp only [CollatzResearch.WordTrace]
  refine ⟨1374028956020835162044381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3664077216055560432118349 1374028956020835162044381)
  ·
    refine ⟨515260858507813185766643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1374028956020835162044381 515260858507813185766643)
    ·
      refine ⟨772891287761719778649965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 515260858507813185766643 772891287761719778649965)
      ·
        refine ⟨289834232910644916993737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 772891287761719778649965 289834232910644916993737)
        ·
          refine ⟨217375674682983687745303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289834232910644916993737 217375674682983687745303)
          ·
            refine ⟨326063512024475531617955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217375674682983687745303 326063512024475531617955)
            ·
              refine ⟨489095268036713297426933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326063512024475531617955 489095268036713297426933)
              ·
                refine ⟨45852681378441871633775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 489095268036713297426933 45852681378441871633775)
                ·
                  rfl

theorem cell19_150690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_150690 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150690 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150690 prefixEnd_150690 := by exact prefixLift 150690
  have htrace : WordTrace (prefixWord ++ tailWord_150690) baseStart_150690 baseEnd_150690 := by
    simpa [prefixWord, tailWord_150690, baseEnd_150690] using wordTrace_append hprefix tailTrace_150690
  have hstable : (prefixWord ++ tailWord_150690).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150690).length < 2 ^ (prefixWord ++ tailWord_150690).sum := by decide
  have hdescent : baseEnd_150690 < baseStart_150690 := by decide
  rcases family_descends (prefixWord ++ tailWord_150690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150692 : List Nat := [2, 3, 1, 2, 3, 2, 1, 5]
def baseStart_150692 : Nat := 118140960795 + 150692 * 2 ^ 59
def prefixEnd_150692 : Nat := 4983230072969 + 3 ^ 40 * 150692 * 2
def baseEnd_150692 : Nat := 45853289948106459589325

theorem tailTrace_150692 : CollatzResearch.WordTrace tailWord_150692 prefixEnd_150692 45853289948106459589325 := by
  unfold tailWord_150692
  simp only [CollatzResearch.WordTrace]
  refine ⟨2748094385038047494875165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3664125846717396659833553 2748094385038047494875165)
  ·
    refine ⟨1030535394389267810578187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2748094385038047494875165 1030535394389267810578187)
    ·
      refine ⟨1545803091583901715867281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1030535394389267810578187 1545803091583901715867281)
      ·
        refine ⟨1159352318687926286900461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1545803091583901715867281 1159352318687926286900461)
        ·
          refine ⟨434757119507972357587673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1159352318687926286900461 434757119507972357587673)
          ·
            refine ⟨326067839630979268190755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 434757119507972357587673 326067839630979268190755)
            ·
              refine ⟨489101759446468902286133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326067839630979268190755 489101759446468902286133)
              ·
                refine ⟨45853289948106459589325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 489101759446468902286133 45853289948106459589325)
                ·
                  rfl

theorem cell19_150692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_150692 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150692 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150692 prefixEnd_150692 := by exact prefixLift 150692
  have htrace : WordTrace (prefixWord ++ tailWord_150692) baseStart_150692 baseEnd_150692 := by
    simpa [prefixWord, tailWord_150692, baseEnd_150692] using wordTrace_append hprefix tailTrace_150692
  have hstable : (prefixWord ++ tailWord_150692).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150692).length < 2 ^ (prefixWord ++ tailWord_150692).sum := by decide
  have hdescent : baseEnd_150692 < baseStart_150692 := by decide
  rcases family_descends (prefixWord ++ tailWord_150692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150713 : List Nat := [1, 2, 1, 4, 1, 3, 7]
def baseStart_150713 : Nat := 118140960795 + 150713 * 2 ^ 59
def prefixEnd_150713 : Nat := 4983230072969 + 3 ^ 40 * 150713 * 2
def baseEnd_150713 : Nat := 15286559976528211040867

theorem tailTrace_150713 : CollatzResearch.WordTrace tailWord_150713 prefixEnd_150713 15286559976528211040867 := by
  unfold tailWord_150713
  simp only [CollatzResearch.WordTrace]
  refine ⟨5496954703000015576264793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3664636468666677050843195 5496954703000015576264793)
  ·
    refine ⟨4122716027250011682198595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5496954703000015576264793 4122716027250011682198595)
    ·
      refine ⟨6184074040875017523297893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4122716027250011682198595 6184074040875017523297893)
      ·
        refine ⟨1159513882664065785618355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6184074040875017523297893 1159513882664065785618355)
        ·
          refine ⟨1739270823996098678427533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1159513882664065785618355 1739270823996098678427533)
          ·
            refine ⟨652226558998537004410325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1739270823996098678427533 652226558998537004410325)
            ·
              refine ⟨15286559976528211040867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 652226558998537004410325 15286559976528211040867)
              ·
                rfl

theorem cell19_150713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 7].length) (baseStart_150713 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150713 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150713 prefixEnd_150713 := by exact prefixLift 150713
  have htrace : WordTrace (prefixWord ++ tailWord_150713) baseStart_150713 baseEnd_150713 := by
    simpa [prefixWord, tailWord_150713, baseEnd_150713] using wordTrace_append hprefix tailTrace_150713
  have hstable : (prefixWord ++ tailWord_150713).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150713).length < 2 ^ (prefixWord ++ tailWord_150713).sum := by decide
  have hdescent : baseEnd_150713 < baseStart_150713 := by decide
  rcases family_descends (prefixWord ++ tailWord_150713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150730 : List Nat := [3, 1, 2, 1, 3, 3, 2, 4]
def baseStart_150730 : Nat := 118140960795 + 150730 * 2 ^ 59
def prefixEnd_150730 : Nat := 4983230072969 + 3 ^ 40 * 150730 * 2
def baseEnd_150730 : Nat := 45864852771733630744777

theorem tailTrace_150730 : CollatzResearch.WordTrace tailWord_150730 prefixEnd_150730 45864852771733630744777 := by
  unfold tailWord_150730
  simp only [CollatzResearch.WordTrace]
  refine ⟨1374393685984606869908411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3665049829292284986422429 1374393685984606869908411)
  ·
    refine ⟨2061590528976910304862617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1374393685984606869908411 2061590528976910304862617)
    ·
      refine ⟨1546192896732682728646963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2061590528976910304862617 1546192896732682728646963)
      ·
        refine ⟨2319289345099024092970445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1546192896732682728646963 2319289345099024092970445)
        ·
          refine ⟨869733504412134034863917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2319289345099024092970445 869733504412134034863917)
          ·
            refine ⟨326150064154550263073969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 869733504412134034863917 326150064154550263073969)
            ·
              refine ⟨244612548115912697305477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326150064154550263073969 244612548115912697305477)
              ·
                refine ⟨45864852771733630744777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 244612548115912697305477 45864852771733630744777)
                ·
                  rfl

theorem cell19_150730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_150730 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150730 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150730 prefixEnd_150730 := by exact prefixLift 150730
  have htrace : WordTrace (prefixWord ++ tailWord_150730) baseStart_150730 baseEnd_150730 := by
    simpa [prefixWord, tailWord_150730, baseEnd_150730] using wordTrace_append hprefix tailTrace_150730
  have hstable : (prefixWord ++ tailWord_150730).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150730).length < 2 ^ (prefixWord ++ tailWord_150730).sum := by decide
  have hdescent : baseEnd_150730 < baseStart_150730 := by decide
  rcases family_descends (prefixWord ++ tailWord_150730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150751 : List Nat := [1, 1, 2, 3, 2, 1, 4, 5]
def baseStart_150751 : Nat := 118140960795 + 150751 * 2 ^ 59
def prefixEnd_150751 : Nat := 4983230072969 + 3 ^ 40 * 150751 * 2
def baseEnd_150751 : Nat := 45871242753211804278053

theorem tailTrace_150751 : CollatzResearch.WordTrace tailWord_150751 prefixEnd_150751 45871242753211804278053 := by
  unfold tailWord_150751
  simp only [CollatzResearch.WordTrace]
  refine ⟨5498340676862348066148107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3665560451241565377432071 5498340676862348066148107)
  ·
    refine ⟨8247511015293522099222161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5498340676862348066148107 8247511015293522099222161)
    ·
      refine ⟨6185633261470141574416621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8247511015293522099222161 6185633261470141574416621)
      ·
        refine ⟨2319612473051303090406233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6185633261470141574416621 2319612473051303090406233)
        ·
          refine ⟨1739709354788477317804675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2319612473051303090406233 1739709354788477317804675)
          ·
            refine ⟨2609564032182715976707013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1739709354788477317804675 2609564032182715976707013)
            ·
              refine ⟨489293256034259245632565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2609564032182715976707013 489293256034259245632565)
              ·
                refine ⟨45871242753211804278053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 489293256034259245632565 45871242753211804278053)
                ·
                  rfl

theorem cell19_150751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 5].length) (baseStart_150751 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150751 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150751 prefixEnd_150751 := by exact prefixLift 150751
  have htrace : WordTrace (prefixWord ++ tailWord_150751) baseStart_150751 baseEnd_150751 := by
    simpa [prefixWord, tailWord_150751, baseEnd_150751] using wordTrace_append hprefix tailTrace_150751
  have hstable : (prefixWord ++ tailWord_150751).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150751).length < 2 ^ (prefixWord ++ tailWord_150751).sum := by decide
  have hdescent : baseEnd_150751 < baseStart_150751 := by decide
  rcases family_descends (prefixWord ++ tailWord_150751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150770 : List Nat := [3, 2, 1, 3, 10]
def baseStart_150770 : Nat := 118140960795 + 150770 * 2 ^ 59
def prefixEnd_150770 : Nat := 4983230072969 + 3 ^ 40 * 150770 * 2
def baseEnd_150770 : Nat := 1699149043149088513177

theorem tailTrace_150770 : CollatzResearch.WordTrace tailWord_150770 prefixEnd_150770 1699149043149088513177 := by
  unfold tailWord_150770
  simp only [CollatzResearch.WordTrace]
  refine ⟨1374758415948378577772441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3666022442529009540726509 1374758415948378577772441)
  ·
    refine ⟨1031068811961283933329331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1374758415948378577772441 1031068811961283933329331)
    ·
      refine ⟨1546603217941925899993997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1031068811961283933329331 1546603217941925899993997)
      ·
        refine ⟨579976206728222212497749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1546603217941925899993997 579976206728222212497749)
        ·
          refine ⟨1699149043149088513177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 579976206728222212497749 1699149043149088513177)
          ·
            rfl

theorem cell19_150770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 10].length) (baseStart_150770 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150770 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150770 prefixEnd_150770 := by exact prefixLift 150770
  have htrace : WordTrace (prefixWord ++ tailWord_150770) baseStart_150770 baseEnd_150770 := by
    simpa [prefixWord, tailWord_150770, baseEnd_150770] using wordTrace_append hprefix tailTrace_150770
  have hstable : (prefixWord ++ tailWord_150770).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150770).length < 2 ^ (prefixWord ++ tailWord_150770).sum := by decide
  have hdescent : baseEnd_150770 < baseStart_150770 := by decide
  rcases family_descends (prefixWord ++ tailWord_150770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150787 : List Nat := [1, 1, 1, 3, 2, 6, 1, 4]
def baseStart_150787 : Nat := 118140960795 + 150787 * 2 ^ 59
def prefixEnd_150787 : Nat := 4983230072969 + 3 ^ 40 * 150787 * 2
def baseEnd_150787 : Nat := 45882197007174387477955

theorem tailTrace_150787 : CollatzResearch.WordTrace tailWord_150787 prefixEnd_150787 45882197007174387477955 := by
  unfold tailWord_150787
  simp only [CollatzResearch.WordTrace]
  refine ⟨5499653704731926214458615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3666435803154617476305743 5499653704731926214458615)
  ·
    refine ⟨8249480557097889321687923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5499653704731926214458615 8249480557097889321687923)
    ·
      refine ⟨12374220835646833982531885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8249480557097889321687923 12374220835646833982531885)
      ·
        refine ⟨4640332813367562743449457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12374220835646833982531885 4640332813367562743449457)
        ·
          refine ⟨3480249610025672057587093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4640332813367562743449457 3480249610025672057587093)
          ·
            refine ⟨163136700469953377699395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3480249610025672057587093 163136700469953377699395)
            ·
              refine ⟨244705050704930066549093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163136700469953377699395 244705050704930066549093)
              ·
                refine ⟨45882197007174387477955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 244705050704930066549093 45882197007174387477955)
                ·
                  rfl

theorem cell19_150787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 4].length) (baseStart_150787 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150787 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150787 prefixEnd_150787 := by exact prefixLift 150787
  have htrace : WordTrace (prefixWord ++ tailWord_150787) baseStart_150787 baseEnd_150787 := by
    simpa [prefixWord, tailWord_150787, baseEnd_150787] using wordTrace_append hprefix tailTrace_150787
  have hstable : (prefixWord ++ tailWord_150787).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150787).length < 2 ^ (prefixWord ++ tailWord_150787).sum := by decide
  have hdescent : baseEnd_150787 < baseStart_150787 := by decide
  rcases family_descends (prefixWord ++ tailWord_150787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150865 : List Nat := [1, 2, 2, 1, 4, 1, 3, 5]
def baseStart_150865 : Nat := 118140960795 + 150865 * 2 ^ 59
def prefixEnd_150865 : Nat := 4983230072969 + 3 ^ 40 * 150865 * 2
def baseEnd_150865 : Nat := 45905931224093317744409

theorem tailTrace_150865 : CollatzResearch.WordTrace tailWord_150865 prefixEnd_150865 45905931224093317744409 := by
  unfold tailWord_150865
  simp only [CollatzResearch.WordTrace]
  refine ⟨5502498598449345535798049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3668332398966230357198699 5502498598449345535798049)
  ·
    refine ⟨4126873948837009151848537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5502498598449345535798049 4126873948837009151848537)
    ·
      refine ⟨3095155461627756863886403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4126873948837009151848537 3095155461627756863886403)
      ·
        refine ⟨4642733192441635295829605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3095155461627756863886403 4642733192441635295829605)
        ·
          refine ⟨870512473582806617968051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4642733192441635295829605 870512473582806617968051)
          ·
            refine ⟨1305768710374209926952077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 870512473582806617968051 1305768710374209926952077)
            ·
              refine ⟨489663266390328722607029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1305768710374209926952077 489663266390328722607029)
              ·
                refine ⟨45905931224093317744409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 489663266390328722607029 45905931224093317744409)
                ·
                  rfl

theorem cell19_150865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 5].length) (baseStart_150865 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150865 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150865 prefixEnd_150865 := by exact prefixLift 150865
  have htrace : WordTrace (prefixWord ++ tailWord_150865) baseStart_150865 baseEnd_150865 := by
    simpa [prefixWord, tailWord_150865, baseEnd_150865] using wordTrace_append hprefix tailTrace_150865
  have hstable : (prefixWord ++ tailWord_150865).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150865).length < 2 ^ (prefixWord ++ tailWord_150865).sum := by decide
  have hdescent : baseEnd_150865 < baseStart_150865 := by decide
  rcases family_descends (prefixWord ++ tailWord_150865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150884 : List Nat := [2, 3, 1, 1, 3, 2, 7]
def baseStart_150884 : Nat := 118140960795 + 150884 * 2 ^ 59
def prefixEnd_150884 : Nat := 4983230072969 + 3 ^ 40 * 150884 * 2
def baseEnd_150884 : Nat := 15303904211968967774045

theorem tailTrace_150884 : CollatzResearch.WordTrace tailWord_150884 prefixEnd_150884 15303904211968967774045 := by
  unfold tailWord_150884
  simp only [CollatzResearch.WordTrace]
  refine ⟨2751595792690255890369853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3668794390253674520493137 2751595792690255890369853)
  ·
    refine ⟨1031848422258845958888695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2751595792690255890369853 1031848422258845958888695)
    ·
      refine ⟨1547772633388268938333043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1031848422258845958888695 1547772633388268938333043)
      ·
        refine ⟨2321658950082403407499565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1547772633388268938333043 2321658950082403407499565)
        ·
          refine ⟨870622106280901277812337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2321658950082403407499565 870622106280901277812337)
          ·
            refine ⟨652966579710675958359253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 870622106280901277812337 652966579710675958359253)
            ·
              refine ⟨15303904211968967774045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 652966579710675958359253 15303904211968967774045)
              ·
                rfl

theorem cell19_150884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 7].length) (baseStart_150884 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150884 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150884 prefixEnd_150884 := by exact prefixLift 150884
  have htrace : WordTrace (prefixWord ++ tailWord_150884) baseStart_150884 baseEnd_150884 := by
    simpa [prefixWord, tailWord_150884, baseEnd_150884] using wordTrace_append hprefix tailTrace_150884
  have hstable : (prefixWord ++ tailWord_150884).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150884).length < 2 ^ (prefixWord ++ tailWord_150884).sum := by decide
  have hdescent : baseEnd_150884 < baseStart_150884 := by decide
  rcases family_descends (prefixWord ++ tailWord_150884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150903 : List Nat := [1, 1, 3, 1, 1, 2, 6, 4]
def baseStart_150903 : Nat := 118140960795 + 150903 * 2 ^ 59
def prefixEnd_150903 : Nat := 4983230072969 + 3 ^ 40 * 150903 * 2
def baseEnd_150903 : Nat := 45917494047720488899861

theorem tailTrace_150903 : CollatzResearch.WordTrace tailWord_150903 prefixEnd_150903 45917494047720488899861 := by
  unfold tailWord_150903
  simp only [CollatzResearch.WordTrace]
  refine ⟨5503884572311678025681363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3669256381541118683787575 5503884572311678025681363)
  ·
    refine ⟨8255826858467517038522045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5503884572311678025681363 8255826858467517038522045)
    ·
      refine ⟨3095935071925318889445767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8255826858467517038522045 3095935071925318889445767)
      ·
        refine ⟨4643902607887978334168651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3095935071925318889445767 4643902607887978334168651)
        ·
          refine ⟨6965853911831967501252977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4643902607887978334168651 6965853911831967501252977)
          ·
            refine ⟨5224390433873975625939733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6965853911831967501252977 5224390433873975625939733)
            ·
              refine ⟨244893301587842607465925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5224390433873975625939733 244893301587842607465925)
              ·
                refine ⟨45917494047720488899861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 244893301587842607465925 45917494047720488899861)
                ·
                  rfl

theorem cell19_150903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 4].length) (baseStart_150903 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150903 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150903 prefixEnd_150903 := by exact prefixLift 150903
  have htrace : WordTrace (prefixWord ++ tailWord_150903) baseStart_150903 baseEnd_150903 := by
    simpa [prefixWord, tailWord_150903, baseEnd_150903] using wordTrace_append hprefix tailTrace_150903
  have hstable : (prefixWord ++ tailWord_150903).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150903).length < 2 ^ (prefixWord ++ tailWord_150903).sum := by decide
  have hdescent : baseEnd_150903 < baseStart_150903 := by decide
  rcases family_descends (prefixWord ++ tailWord_150903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150941 : List Nat := [1, 4, 2, 1, 3, 8]
def baseStart_150941 : Nat := 118140960795 + 150941 * 2 ^ 59
def prefixEnd_150941 : Nat := 4983230072969 + 3 ^ 40 * 150941 * 2
def baseEnd_150941 : Nat := 5103228541260851117257

theorem tailTrace_150941 : CollatzResearch.WordTrace tailWord_150941 prefixEnd_150941 5103228541260851117257 := by
  unfold tailWord_150941
  simp only [CollatzResearch.WordTrace]
  refine ⟨5505270546174010515564677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3670180364116007010376451 5505270546174010515564677)
  ·
    refine ⟨1032238227407626971668377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5505270546174010515564677 1032238227407626971668377)
    ·
      refine ⟨774178670555720228751283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1032238227407626971668377 774178670555720228751283)
      ·
        refine ⟨1161268005833580343126925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 774178670555720228751283 1161268005833580343126925)
        ·
          refine ⟨435475502187592628672597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1161268005833580343126925 435475502187592628672597)
          ·
            refine ⟨5103228541260851117257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 435475502187592628672597 5103228541260851117257)
            ·
              rfl

theorem cell19_150941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 8].length) (baseStart_150941 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150941 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150941 prefixEnd_150941 := by exact prefixLift 150941
  have htrace : WordTrace (prefixWord ++ tailWord_150941) baseStart_150941 baseEnd_150941 := by
    simpa [prefixWord, tailWord_150941, baseEnd_150941] using wordTrace_append hprefix tailTrace_150941
  have hstable : (prefixWord ++ tailWord_150941).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150941).length < 2 ^ (prefixWord ++ tailWord_150941).sum := by decide
  have hdescent : baseEnd_150941 < baseStart_150941 := by decide
  rcases family_descends (prefixWord ++ tailWord_150941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150996 : List Nat := [2, 4, 1, 2, 3, 1, 6]
def baseStart_150996 : Nat := 118140960795 + 150996 * 2 ^ 59
def prefixEnd_150996 : Nat := 4983230072969 + 3 ^ 40 * 150996 * 2
def baseEnd_150996 : Nat := 15315264179041276277647

theorem tailTrace_150996 : CollatzResearch.WordTrace tailWord_150996 prefixEnd_150996 15315264179041276277647 := by
  unfold tailWord_150996
  simp only [CollatzResearch.WordTrace]
  refine ⟨2753638280487377454408421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3671517707316503272544561 2753638280487377454408421)
  ·
    refine ⟨516307177591383272701579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2753638280487377454408421 516307177591383272701579)
    ·
      refine ⟨774460766387074909052369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 516307177591383272701579 774460766387074909052369)
      ·
        refine ⟨580845574790306181789277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 774460766387074909052369 580845574790306181789277)
        ·
          refine ⟨217817090546364818170979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 580845574790306181789277 217817090546364818170979)
          ·
            refine ⟨326725635819547227256469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217817090546364818170979 326725635819547227256469)
            ·
              refine ⟨15315264179041276277647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 326725635819547227256469 15315264179041276277647)
              ·
                rfl

theorem cell19_150996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 6].length) (baseStart_150996 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_150996 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_150996 prefixEnd_150996 := by exact prefixLift 150996
  have htrace : WordTrace (prefixWord ++ tailWord_150996) baseStart_150996 baseEnd_150996 := by
    simpa [prefixWord, tailWord_150996, baseEnd_150996] using wordTrace_append hprefix tailTrace_150996
  have hstable : (prefixWord ++ tailWord_150996).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150996).length < 2 ^ (prefixWord ++ tailWord_150996).sum := by decide
  have hdescent : baseEnd_150996 < baseStart_150996 := by decide
  rcases family_descends (prefixWord ++ tailWord_150996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151072 : List Nat := [2, 1, 1, 6, 1, 2, 2, 4]
def baseStart_151072 : Nat := 118140960795 + 151072 * 2 ^ 59
def prefixEnd_151072 : Nat := 4983230072969 + 3 ^ 40 * 151072 * 2
def baseEnd_151072 : Nat := 45968918184378171143845

theorem tailTrace_151072 : CollatzResearch.WordTrace tailWord_151072 prefixEnd_151072 45968918184378171143845 := by
  unfold tailWord_151072
  simp only [CollatzResearch.WordTrace]
  refine ⟨2755024254349709944291735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3673365672466279925722313 2755024254349709944291735)
  ·
    refine ⟨4132536381524564916437603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2755024254349709944291735 4132536381524564916437603)
    ·
      refine ⟨6198804572286847374656405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4132536381524564916437603 6198804572286847374656405)
      ·
        refine ⟨290568964325945970687019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6198804572286847374656405 290568964325945970687019)
        ·
          refine ⟨435853446488918956030529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290568964325945970687019 435853446488918956030529)
          ·
            refine ⟨326890084866689217022897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 435853446488918956030529 326890084866689217022897)
            ·
              refine ⟨245167563650016912767173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326890084866689217022897 245167563650016912767173)
              ·
                refine ⟨45968918184378171143845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 245167563650016912767173 45968918184378171143845)
                ·
                  rfl

theorem cell19_151072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_151072 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_151072 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_151072 prefixEnd_151072 := by exact prefixLift 151072
  have htrace : WordTrace (prefixWord ++ tailWord_151072) baseStart_151072 baseEnd_151072 := by
    simpa [prefixWord, tailWord_151072, baseEnd_151072] using wordTrace_append hprefix tailTrace_151072
  have hstable : (prefixWord ++ tailWord_151072).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151072).length < 2 ^ (prefixWord ++ tailWord_151072).sum := by decide
  have hdescent : baseEnd_151072 < baseStart_151072 := by decide
  rcases family_descends (prefixWord ++ tailWord_151072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151074 : List Nat := [3, 3, 1, 1, 1, 1, 3, 6]
def baseStart_151074 : Nat := 118140960795 + 151074 * 2 ^ 59
def prefixEnd_151074 : Nat := 4983230072969 + 3 ^ 40 * 151074 * 2
def baseEnd_151074 : Nat := 45969526754042759099395

theorem tailTrace_151074 : CollatzResearch.WordTrace tailWord_151074 prefixEnd_151074 45969526754042759099395 := by
  unfold tailWord_151074
  simp only [CollatzResearch.WordTrace]
  refine ⟨1377530363673043557539069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3673414303128116153437517 1377530363673043557539069)
  ·
    refine ⟨516573886377391334077151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1377530363673043557539069 516573886377391334077151)
    ·
      refine ⟨774860829566087001115727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 516573886377391334077151 774860829566087001115727)
      ·
        refine ⟨1162291244349130501673591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 774860829566087001115727 1162291244349130501673591)
        ·
          refine ⟨1743436866523695752510387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1162291244349130501673591 1743436866523695752510387)
          ·
            refine ⟨2615155299785543628765581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1743436866523695752510387 2615155299785543628765581)
            ·
              refine ⟨980683237419578860787093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2615155299785543628765581 980683237419578860787093)
              ·
                refine ⟨45969526754042759099395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 980683237419578860787093 45969526754042759099395)
                ·
                  rfl

theorem cell19_151074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_151074 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_151074 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_151074 prefixEnd_151074 := by exact prefixLift 151074
  have htrace : WordTrace (prefixWord ++ tailWord_151074) baseStart_151074 baseEnd_151074 := by
    simpa [prefixWord, tailWord_151074, baseEnd_151074] using wordTrace_append hprefix tailTrace_151074
  have hstable : (prefixWord ++ tailWord_151074).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151074).length < 2 ^ (prefixWord ++ tailWord_151074).sum := by decide
  have hdescent : baseEnd_151074 < baseStart_151074 := by decide
  rcases family_descends (prefixWord ++ tailWord_151074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151093 : List Nat := [1, 3, 3, 1, 1, 3, 2, 5]
def baseStart_151093 : Nat := 118140960795 + 151093 * 2 ^ 59
def prefixEnd_151093 : Nat := 4983230072969 + 3 ^ 40 * 151093 * 2
def baseEnd_151093 : Nat := 45975308165856344677121

theorem tailTrace_151093 : CollatzResearch.WordTrace tailWord_151093 prefixEnd_151093 45975308165856344677121 := by
  unfold tailWord_151093
  simp only [CollatzResearch.WordTrace]
  refine ⟨5510814441623340475097933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3673876294415560316731955 5510814441623340475097933)
  ·
    refine ⟨2066555415608752678161725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5510814441623340475097933 2066555415608752678161725)
    ·
      refine ⟨774958280853282254310647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2066555415608752678161725 774958280853282254310647)
      ·
        refine ⟨1162437421279923381465971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 774958280853282254310647 1162437421279923381465971)
        ·
          refine ⟨1743656131919885072198957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1162437421279923381465971 1743656131919885072198957)
          ·
            refine ⟨653871049469956902074609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1743656131919885072198957 653871049469956902074609)
            ·
              refine ⟨490403287102467676555957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 653871049469956902074609 490403287102467676555957)
              ·
                refine ⟨45975308165856344677121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 490403287102467676555957 45975308165856344677121)
                ·
                  rfl

theorem cell19_151093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 5].length) (baseStart_151093 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_151093 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_151093 prefixEnd_151093 := by exact prefixLift 151093
  have htrace : WordTrace (prefixWord ++ tailWord_151093) baseStart_151093 baseEnd_151093 := by
    simpa [prefixWord, tailWord_151093, baseEnd_151093] using wordTrace_append hprefix tailTrace_151093
  have hstable : (prefixWord ++ tailWord_151093).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151093).length < 2 ^ (prefixWord ++ tailWord_151093).sum := by decide
  have hdescent : baseEnd_151093 < baseStart_151093 := by decide
  rcases family_descends (prefixWord ++ tailWord_151093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151110 : List Nat := [6, 1, 1, 1, 10]
def baseStart_151110 : Nat := 118140960795 + 151110 * 2 ^ 59
def prefixEnd_151110 : Nat := 4983230072969 + 3 ^ 40 * 151110 * 2
def baseEnd_151110 : Nat := 1702980778074271937011

theorem tailTrace_151110 : CollatzResearch.WordTrace tailWord_151110 prefixEnd_151110 1702980778074271937011 := by
  unfold tailWord_151110
  simp only [CollatzResearch.WordTrace]
  refine ⟨172232327580054761827087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3674289655041168252311189 172232327580054761827087)
  ·
    refine ⟨258348491370082142740631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172232327580054761827087 258348491370082142740631)
    ·
      refine ⟨387522737055123214110947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258348491370082142740631 387522737055123214110947)
      ·
        refine ⟨581284105582684821166421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387522737055123214110947 581284105582684821166421)
        ·
          refine ⟨1702980778074271937011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 581284105582684821166421 1702980778074271937011)
          ·
            rfl

theorem cell19_151110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 10].length) (baseStart_151110 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_151110 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_151110 prefixEnd_151110 := by exact prefixLift 151110
  have htrace : WordTrace (prefixWord ++ tailWord_151110) baseStart_151110 baseEnd_151110 := by
    simpa [prefixWord, tailWord_151110, baseEnd_151110] using wordTrace_append hprefix tailTrace_151110
  have hstable : (prefixWord ++ tailWord_151110).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151110).length < 2 ^ (prefixWord ++ tailWord_151110).sum := by decide
  have hdescent : baseEnd_151110 < baseStart_151110 := by decide
  rcases family_descends (prefixWord ++ tailWord_151110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151169 : List Nat := [1, 2, 4, 2, 1, 3, 6]
def baseStart_151169 : Nat := 118140960795 + 151169 * 2 ^ 59
def prefixEnd_151169 : Nat := 4983230072969 + 3 ^ 40 * 151169 * 2
def baseEnd_151169 : Nat := 15332811271036895662675

theorem tailTrace_151169 : CollatzResearch.WordTrace tailWord_151169 prefixEnd_151169 15332811271036895662675 := by
  unfold tailWord_151169
  simp only [CollatzResearch.WordTrace]
  refine ⟨5513586389348005454864561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3675724259565336969909707 5513586389348005454864561)
  ·
    refine ⟨4135189792011004091148421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5513586389348005454864561 4135189792011004091148421)
    ·
      refine ⟨775348086002063267090329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4135189792011004091148421 775348086002063267090329)
      ·
        refine ⟨581511064501547450317747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 775348086002063267090329 581511064501547450317747)
        ·
          refine ⟨872266596752321175476621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 581511064501547450317747 872266596752321175476621)
          ·
            refine ⟨327099973782120440803733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 872266596752321175476621 327099973782120440803733)
            ·
              refine ⟨15332811271036895662675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 327099973782120440803733 15332811271036895662675)
              ·
                rfl

theorem cell19_151169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 6].length) (baseStart_151169 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_151169 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_151169 prefixEnd_151169 := by exact prefixLift 151169
  have htrace : WordTrace (prefixWord ++ tailWord_151169) baseStart_151169 baseEnd_151169 := by
    simpa [prefixWord, tailWord_151169, baseEnd_151169] using wordTrace_append hprefix tailTrace_151169
  have hstable : (prefixWord ++ tailWord_151169).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151169).length < 2 ^ (prefixWord ++ tailWord_151169).sum := by decide
  have hdescent : baseEnd_151169 < baseStart_151169 := by decide
  rcases family_descends (prefixWord ++ tailWord_151169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151222 : List Nat := [5, 1, 3, 1, 1, 3, 5]
def baseStart_151222 : Nat := 118140960795 + 151222 * 2 ^ 59
def prefixEnd_151222 : Nat := 4983230072969 + 3 ^ 40 * 151222 * 2
def baseEnd_151222 : Nat := 15338186969740755936701

theorem tailTrace_151222 : CollatzResearch.WordTrace tailWord_151222 prefixEnd_151222 15338186969740755936701 := by
  unfold tailWord_151222
  simp only [CollatzResearch.WordTrace]
  refine ⟨344719966134749719158995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3677012972103997004362613 344719966134749719158995)
  ·
    refine ⟨517079949202124578738493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 344719966134749719158995 517079949202124578738493)
    ·
      refine ⟨193904980950796717026935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 517079949202124578738493 193904980950796717026935)
      ·
        refine ⟨290857471426195075540403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193904980950796717026935 290857471426195075540403)
        ·
          refine ⟨436286207139292613310605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290857471426195075540403 436286207139292613310605)
          ·
            refine ⟨163607327677234729991477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 436286207139292613310605 163607327677234729991477)
            ·
              refine ⟨15338186969740755936701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 163607327677234729991477 15338186969740755936701)
              ·
                rfl

theorem cell19_151222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 5].length) (baseStart_151222 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_151222 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_151222 prefixEnd_151222 := by exact prefixLift 151222
  have htrace : WordTrace (prefixWord ++ tailWord_151222) baseStart_151222 baseEnd_151222 := by
    simpa [prefixWord, tailWord_151222, baseEnd_151222] using wordTrace_append hprefix tailTrace_151222
  have hstable : (prefixWord ++ tailWord_151222).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151222).length < 2 ^ (prefixWord ++ tailWord_151222).sum := by decide
  have hdescent : baseEnd_151222 < baseStart_151222 := by decide
  rcases family_descends (prefixWord ++ tailWord_151222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
