import V185TrunkScan22Chunk138

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1245248 : List Nat := [2, 1, 1, 2, 2, 4, 3, 1, 6]
def baseStart_1245248 : Nat := 118140960795 + 1245248 * 2 ^ 59
def prefixEnd_1245248 : Nat := 4983230072969 + 3 ^ 40 * 1245248 * 2
def baseEnd_1245248 : Nat := 142091279566677598927381

theorem tailTrace_1245248 : CollatzResearch.WordTrace tailWord_1245248 prefixEnd_1245248 142091279566677598927381 := by
  unfold tailWord_1245248
  simp only [CollatzResearch.WordTrace]
  refine ⟨22708962896343321135936199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30278617195124428181248265 22708962896343321135936199)
  ·
    refine ⟨34063444344514981703904299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22708962896343321135936199 34063444344514981703904299)
    ·
      refine ⟨51095166516772472555856449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34063444344514981703904299 51095166516772472555856449)
      ·
        refine ⟨38321374887579354416892337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51095166516772472555856449 38321374887579354416892337)
        ·
          refine ⟨28741031165684515812669253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38321374887579354416892337 28741031165684515812669253)
          ·
            refine ⟨5388943343565846714875485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28741031165684515812669253 5388943343565846714875485)
            ·
              refine ⟨2020853753837192518078307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5388943343565846714875485 2020853753837192518078307)
              ·
                refine ⟨3031280630755788777117461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2020853753837192518078307 3031280630755788777117461)
                ·
                  refine ⟨142091279566677598927381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3031280630755788777117461 142091279566677598927381)
                  ·
                    rfl

theorem cell22_1245248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 6].length) (baseStart_1245248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1245248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1245248 prefixEnd_1245248 := by exact prefixLift 1245248
  have htrace : WordTrace (prefixWord ++ tailWord_1245248) baseStart_1245248 baseEnd_1245248 := by
    simpa [prefixWord, tailWord_1245248, baseEnd_1245248] using wordTrace_append hprefix tailTrace_1245248
  have hstable : (prefixWord ++ tailWord_1245248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245248).length < 2 ^ (prefixWord ++ tailWord_1245248).sum := by decide
  have hdescent : baseEnd_1245248 < baseStart_1245248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245410 : List Nat := [3, 3, 4, 1, 2, 1, 1, 1, 3, 3]
def baseStart_1245410 : Nat := 118140960795 + 1245410 * 2 ^ 59
def prefixEnd_1245410 : Nat := 4983230072969 + 3 ^ 40 * 1245410 * 2
def baseEnd_1245410 : Nat := 426329294610718374231647

theorem tailTrace_1245410 : CollatzResearch.WordTrace tailWord_1245410 prefixEnd_1245410 426329294610718374231647 := by
  unfold tailWord_1245410
  simp only [CollatzResearch.WordTrace]
  refine ⟨11355958604524935984817421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30282556278733162626179789 11355958604524935984817421)
  ·
    refine ⟨4258484476696850994306533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11355958604524935984817421 4258484476696850994306533)
    ·
      refine ⟨798465839380659561432475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4258484476696850994306533 798465839380659561432475)
      ·
        refine ⟨1197698759070989342148713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 798465839380659561432475 1197698759070989342148713)
        ·
          refine ⟨898274069303242006611535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1197698759070989342148713 898274069303242006611535)
          ·
            refine ⟨1347411103954863009917303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 898274069303242006611535 1347411103954863009917303)
            ·
              refine ⟨2021116655932294514875955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1347411103954863009917303 2021116655932294514875955)
              ·
                refine ⟨3031674983898441772313933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2021116655932294514875955 3031674983898441772313933)
                ·
                  refine ⟨1136878118961915664617725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3031674983898441772313933 1136878118961915664617725)
                  ·
                    refine ⟨426329294610718374231647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1136878118961915664617725 426329294610718374231647)
                    ·
                      rfl

theorem cell22_1245410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_1245410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1245410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1245410 prefixEnd_1245410 := by exact prefixLift 1245410
  have htrace : WordTrace (prefixWord ++ tailWord_1245410) baseStart_1245410 baseEnd_1245410 := by
    simpa [prefixWord, tailWord_1245410, baseEnd_1245410] using wordTrace_append hprefix tailTrace_1245410
  have hstable : (prefixWord ++ tailWord_1245410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245410).length < 2 ^ (prefixWord ++ tailWord_1245410).sum := by decide
  have hdescent : baseEnd_1245410 < baseStart_1245410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245430 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 3, 6]
def baseStart_1245430 : Nat := 118140960795 + 1245430 * 2 ^ 59
def prefixEnd_1245430 : Nat := 4983230072969 + 3 ^ 40 * 1245430 * 2
def baseEnd_1245430 : Nat := 426336141019444988731585

theorem tailTrace_1245430 : CollatzResearch.WordTrace tailWord_1245430 prefixEnd_1245430 426336141019444988731585 := by
  unfold tailWord_1245430
  simp only [CollatzResearch.WordTrace]
  refine ⟨2839035242376705459687359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30283042585351524903331829 2839035242376705459687359)
  ·
    refine ⟨4258552863565058189531039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2839035242376705459687359 4258552863565058189531039)
    ·
      refine ⟨6387829295347587284296559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4258552863565058189531039 6387829295347587284296559)
      ·
        refine ⟨9581743943021380926444839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6387829295347587284296559 9581743943021380926444839)
        ·
          refine ⟨14372615914532071389667259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9581743943021380926444839 14372615914532071389667259)
          ·
            refine ⟨21558923871798107084500889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14372615914532071389667259 21558923871798107084500889)
            ·
              refine ⟨16169192903848580313375667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21558923871798107084500889 16169192903848580313375667)
              ·
                refine ⟨24253789355772870470063501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16169192903848580313375667 24253789355772870470063501)
                ·
                  refine ⟨9095171008414826426273813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24253789355772870470063501 9095171008414826426273813)
                  ·
                    refine ⟨426336141019444988731585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9095171008414826426273813 426336141019444988731585)
                    ·
                      rfl

theorem cell22_1245430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_1245430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1245430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1245430 prefixEnd_1245430 := by exact prefixLift 1245430
  have htrace : WordTrace (prefixWord ++ tailWord_1245430) baseStart_1245430 baseEnd_1245430 := by
    simpa [prefixWord, tailWord_1245430, baseEnd_1245430] using wordTrace_append hprefix tailTrace_1245430
  have hstable : (prefixWord ++ tailWord_1245430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245430).length < 2 ^ (prefixWord ++ tailWord_1245430).sum := by decide
  have hdescent : baseEnd_1245430 < baseStart_1245430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245524 : List Nat := [2, 4, 1, 1, 2, 4, 1, 2, 5]
def baseStart_1245524 : Nat := 118140960795 + 1245524 * 2 ^ 59
def prefixEnd_1245524 : Nat := 4983230072969 + 3 ^ 40 * 1245524 * 2
def baseEnd_1245524 : Nat := 142122773046820025627099

theorem tailTrace_1245524 : CollatzResearch.WordTrace tailWord_1245524 prefixEnd_1245524 142122773046820025627099 := by
  unfold tailWord_1245524
  simp only [CollatzResearch.WordTrace]
  refine ⟨22713996169843370704459813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30285328226457827605946417 22713996169843370704459813)
  ·
    refine ⟨4258874281845632007086215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22713996169843370704459813 4258874281845632007086215)
    ·
      refine ⟨6388311422768448010629323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4258874281845632007086215 6388311422768448010629323)
      ·
        refine ⟨9582467134152672015943985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6388311422768448010629323 9582467134152672015943985)
        ·
          refine ⟨7186850350614504011957989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9582467134152672015943985 7186850350614504011957989)
          ·
            refine ⟨1347534440740219502242123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7186850350614504011957989 1347534440740219502242123)
            ·
              refine ⟨2021301661110329253363185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1347534440740219502242123 2021301661110329253363185)
              ·
                refine ⟨1515976245832746940022389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2021301661110329253363185 1515976245832746940022389)
                ·
                  refine ⟨142122773046820025627099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1515976245832746940022389 142122773046820025627099)
                  ·
                    rfl

theorem cell22_1245524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_1245524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1245524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1245524 prefixEnd_1245524 := by exact prefixLift 1245524
  have htrace : WordTrace (prefixWord ++ tailWord_1245524) baseStart_1245524 baseEnd_1245524 := by
    simpa [prefixWord, tailWord_1245524, baseEnd_1245524] using wordTrace_append hprefix tailTrace_1245524
  have hstable : (prefixWord ++ tailWord_1245524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245524).length < 2 ^ (prefixWord ++ tailWord_1245524).sum := by decide
  have hdescent : baseEnd_1245524 < baseStart_1245524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245535 : List Nat := [1, 1, 2, 3, 1, 2, 3, 3, 6]
def baseStart_1245535 : Nat := 118140960795 + 1245535 * 2 ^ 59
def prefixEnd_1245535 : Nat := 4983230072969 + 3 ^ 40 * 1245535 * 2
def baseEnd_1245535 : Nat := 142124028221753238285421

theorem tailTrace_1245535 : CollatzResearch.WordTrace tailWord_1245535 prefixEnd_1245535 142124028221753238285421 := by
  unfold tailWord_1245535
  simp only [CollatzResearch.WordTrace]
  refine ⟨45428393542646890287570059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30285595695097926858380039 45428393542646890287570059)
  ·
    refine ⟨68142590313970335431355089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45428393542646890287570059 68142590313970335431355089)
    ·
      refine ⟨51106942735477751573516317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68142590313970335431355089 51106942735477751573516317)
      ·
        refine ⟨19165103525804156840068619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51106942735477751573516317 19165103525804156840068619)
        ·
          refine ⟨28747655288706235260102929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19165103525804156840068619 28747655288706235260102929)
          ·
            refine ⟨21560741466529676445077197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28747655288706235260102929 21560741466529676445077197)
            ·
              refine ⟨8085278049948628666903949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21560741466529676445077197 8085278049948628666903949)
              ·
                refine ⟨3031979268730735750088981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8085278049948628666903949 3031979268730735750088981)
                ·
                  refine ⟨142124028221753238285421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3031979268730735750088981 142124028221753238285421)
                  ·
                    rfl

theorem cell22_1245535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 6].length) (baseStart_1245535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1245535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1245535 prefixEnd_1245535 := by exact prefixLift 1245535
  have htrace : WordTrace (prefixWord ++ tailWord_1245535) baseStart_1245535 baseEnd_1245535 := by
    simpa [prefixWord, tailWord_1245535, baseEnd_1245535] using wordTrace_append hprefix tailTrace_1245535
  have hstable : (prefixWord ++ tailWord_1245535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245535).length < 2 ^ (prefixWord ++ tailWord_1245535).sum := by decide
  have hdescent : baseEnd_1245535 < baseStart_1245535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245554 : List Nat := [3, 2, 1, 2, 1, 4, 2, 2, 1, 4]
def baseStart_1245554 : Nat := 118140960795 + 1245554 * 2 ^ 59
def prefixEnd_1245554 : Nat := 4983230072969 + 3 ^ 40 * 1245554 * 2
def baseEnd_1245554 : Nat := 426378588753549998631205

theorem tailTrace_1245554 : CollatzResearch.WordTrace tailWord_1245554 prefixEnd_1245554 426378588753549998631205 := by
  unfold tailWord_1245554
  simp only [CollatzResearch.WordTrace]
  refine ⟨11357271632394514133127929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30286057686385371021674477 11357271632394514133127929)
  ·
    refine ⟨8517953724295885599845947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11357271632394514133127929 8517953724295885599845947)
    ·
      refine ⟨12776930586443828399768921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8517953724295885599845947 12776930586443828399768921)
      ·
        refine ⟨9582697939832871299826691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12776930586443828399768921 9582697939832871299826691)
        ·
          refine ⟨14374046909749306949740037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9582697939832871299826691 14374046909749306949740037)
          ·
            refine ⟨2695133795577995053076257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14374046909749306949740037 2695133795577995053076257)
            ·
              refine ⟨2021350346683496289807193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2695133795577995053076257 2021350346683496289807193)
              ·
                refine ⟨1516012760012622217355395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2021350346683496289807193 1516012760012622217355395)
                ·
                  refine ⟨2274019140018933326033093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1516012760012622217355395 2274019140018933326033093)
                  ·
                    refine ⟨426378588753549998631205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2274019140018933326033093 426378588753549998631205)
                    ·
                      rfl

theorem cell22_1245554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_1245554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1245554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1245554 prefixEnd_1245554 := by exact prefixLift 1245554
  have htrace : WordTrace (prefixWord ++ tailWord_1245554) baseStart_1245554 baseEnd_1245554 := by
    simpa [prefixWord, tailWord_1245554, baseEnd_1245554] using wordTrace_append hprefix tailTrace_1245554
  have hstable : (prefixWord ++ tailWord_1245554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245554).length < 2 ^ (prefixWord ++ tailWord_1245554).sum := by decide
  have hdescent : baseEnd_1245554 < baseStart_1245554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245580 : List Nat := [2, 2, 1, 2, 1, 4, 10]
def baseStart_1245580 : Nat := 118140960795 + 1245580 * 2 ^ 59
def prefixEnd_1245580 : Nat := 4983230072969 + 3 ^ 40 * 1245580 * 2
def baseEnd_1245580 : Nat := 15792129225366466573375

theorem tailTrace_1245580 : CollatzResearch.WordTrace tailWord_1245580 prefixEnd_1245580 15792129225366466573375 := by
  unfold tailWord_1245580
  simp only [CollatzResearch.WordTrace]
  refine ⟨22715017413741931486479097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30286689884989241981972129 22715017413741931486479097)
  ·
    refine ⟨17036263060306448614859323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22715017413741931486479097 17036263060306448614859323)
    ·
      refine ⟨25554394590459672922288985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17036263060306448614859323 25554394590459672922288985)
      ·
        refine ⟨19165795942844754691716739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25554394590459672922288985 19165795942844754691716739)
        ·
          refine ⟨28748693914267132037575109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19165795942844754691716739 28748693914267132037575109)
          ·
            refine ⟨5390380108925087257045333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28748693914267132037575109 5390380108925087257045333)
            ·
              refine ⟨15792129225366466573375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5390380108925087257045333 15792129225366466573375)
              ·
                rfl

theorem cell22_1245580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 10].length) (baseStart_1245580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1245580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1245580 prefixEnd_1245580 := by exact prefixLift 1245580
  have htrace : WordTrace (prefixWord ++ tailWord_1245580) baseStart_1245580 baseEnd_1245580 := by
    simpa [prefixWord, tailWord_1245580, baseEnd_1245580] using wordTrace_append hprefix tailTrace_1245580
  have hstable : (prefixWord ++ tailWord_1245580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245580).length < 2 ^ (prefixWord ++ tailWord_1245580).sum := by decide
  have hdescent : baseEnd_1245580 < baseStart_1245580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245612 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 5, 3]
def baseStart_1245612 : Nat := 118140960795 + 1245612 * 2 ^ 59
def prefixEnd_1245612 : Nat := 4983230072969 + 3 ^ 40 * 1245612 * 2
def baseEnd_1245612 : Nat := 426398443338857180681027

theorem tailTrace_1245612 : CollatzResearch.WordTrace tailWord_1245612 prefixEnd_1245612 426398443338857180681027 := by
  unfold tailWord_1245612
  simp only [CollatzResearch.WordTrace]
  refine ⟨22715600981683966219061545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30287467975578621625415393 22715600981683966219061545)
  ·
    refine ⟨17036700736262974664296159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22715600981683966219061545 17036700736262974664296159)
    ·
      refine ⟨25555051104394461996444239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17036700736262974664296159 25555051104394461996444239)
      ·
        refine ⟨38332576656591692994666359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25555051104394461996444239 38332576656591692994666359)
        ·
          refine ⟨57498864984887539491999539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38332576656591692994666359 57498864984887539491999539)
          ·
            refine ⟨86248297477331309237999309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57498864984887539491999539 86248297477331309237999309)
            ·
              refine ⟨32343111553999240964249741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86248297477331309237999309 32343111553999240964249741)
              ·
                refine ⟨12128666832749715361593653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32343111553999240964249741 12128666832749715361593653)
                ·
                  refine ⟨1137062515570285815149405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12128666832749715361593653 1137062515570285815149405)
                  ·
                    refine ⟨426398443338857180681027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1137062515570285815149405 426398443338857180681027)
                    ·
                      rfl

theorem cell22_1245612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 3].length) (baseStart_1245612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1245612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1245612 prefixEnd_1245612 := by exact prefixLift 1245612
  have htrace : WordTrace (prefixWord ++ tailWord_1245612) baseStart_1245612 baseEnd_1245612 := by
    simpa [prefixWord, tailWord_1245612, baseEnd_1245612] using wordTrace_append hprefix tailTrace_1245612
  have hstable : (prefixWord ++ tailWord_1245612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245612).length < 2 ^ (prefixWord ++ tailWord_1245612).sum := by decide
  have hdescent : baseEnd_1245612 < baseStart_1245612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245657 : List Nat := [1, 2, 1, 2, 4, 1, 3, 1, 2, 5]
def baseStart_1245657 : Nat := 118140960795 + 1245657 * 2 ^ 59
def prefixEnd_1245657 : Nat := 4983230072969 + 3 ^ 40 * 1245657 * 2
def baseEnd_1245657 : Nat := 426413847758492063305889

theorem tailTrace_1245657 : CollatzResearch.WordTrace tailWord_1245657 prefixEnd_1245657 426413847758492063305889 := by
  unfold tailWord_1245657
  simp only [CollatzResearch.WordTrace]
  refine ⟨45432843248204905123511225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30288562165469936749007483 45432843248204905123511225)
  ·
    refine ⟨34074632436153678842633419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45432843248204905123511225 34074632436153678842633419)
    ·
      refine ⟨51111948654230518263950129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34074632436153678842633419 51111948654230518263950129)
      ·
        refine ⟨38333961490672888697962597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51111948654230518263950129 38333961490672888697962597)
        ·
          refine ⟨7187617779501166630867987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38333961490672888697962597 7187617779501166630867987)
          ·
            refine ⟨10781426669251749946301981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7187617779501166630867987 10781426669251749946301981)
            ·
              refine ⟨4043035000969406229863243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10781426669251749946301981 4043035000969406229863243)
              ·
                refine ⟨6064552501454109344794865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4043035000969406229863243 6064552501454109344794865)
                ·
                  refine ⟨4548414376090582008596149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6064552501454109344794865 4548414376090582008596149)
                  ·
                    refine ⟨426413847758492063305889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4548414376090582008596149 426413847758492063305889)
                    ·
                      rfl

theorem cell22_1245657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 5].length) (baseStart_1245657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1245657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1245657 prefixEnd_1245657 := by exact prefixLift 1245657
  have htrace : WordTrace (prefixWord ++ tailWord_1245657) baseStart_1245657 baseEnd_1245657 := by
    simpa [prefixWord, tailWord_1245657, baseEnd_1245657] using wordTrace_append hprefix tailTrace_1245657
  have hstable : (prefixWord ++ tailWord_1245657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245657).length < 2 ^ (prefixWord ++ tailWord_1245657).sum := by decide
  have hdescent : baseEnd_1245657 < baseStart_1245657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245717 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 3, 6]
def baseStart_1245717 : Nat := 118140960795 + 1245717 * 2 ^ 59
def prefixEnd_1245717 : Nat := 4983230072969 + 3 ^ 40 * 1245717 * 2
def baseEnd_1245717 : Nat := 426434386984671906805705

theorem tailTrace_1245717 : CollatzResearch.WordTrace tailWord_1245717 prefixEnd_1245717 426434386984671906805705 := by
  unfold tailWord_1245717
  simp only [CollatzResearch.WordTrace]
  refine ⟨45435031627987535370695405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30290021085325023580463603 45435031627987535370695405)
  ·
    refine ⟨17038136860495325764010777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45435031627987535370695405 17038136860495325764010777)
    ·
      refine ⟨12778602645371494323008083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17038136860495325764010777 12778602645371494323008083)
      ·
        refine ⟨19167903968057241484512125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12778602645371494323008083 19167903968057241484512125)
        ·
          refine ⟨7187963988021465556692047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19167903968057241484512125 7187963988021465556692047)
          ·
            refine ⟨10781945982032198335038071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7187963988021465556692047 10781945982032198335038071)
            ·
              refine ⟨16172918973048297502557107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10781945982032198335038071 16172918973048297502557107)
              ·
                refine ⟨24259378459572446253835661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16172918973048297502557107 24259378459572446253835661)
                ·
                  refine ⟨9097266922339667345188373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24259378459572446253835661 9097266922339667345188373)
                  ·
                    refine ⟨426434386984671906805705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9097266922339667345188373 426434386984671906805705)
                    ·
                      rfl

theorem cell22_1245717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_1245717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1245717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1245717 prefixEnd_1245717 := by exact prefixLift 1245717
  have htrace : WordTrace (prefixWord ++ tailWord_1245717) baseStart_1245717 baseEnd_1245717 := by
    simpa [prefixWord, tailWord_1245717, baseEnd_1245717] using wordTrace_append hprefix tailTrace_1245717
  have hstable : (prefixWord ++ tailWord_1245717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245717).length < 2 ^ (prefixWord ++ tailWord_1245717).sum := by decide
  have hdescent : baseEnd_1245717 < baseStart_1245717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245736 : List Nat := [2, 1, 5, 2, 1, 1, 1, 2, 4, 3]
def baseStart_1245736 : Nat := 118140960795 + 1245736 * 2 ^ 59
def prefixEnd_1245736 : Nat := 4983230072969 + 3 ^ 40 * 1245736 * 2
def baseEnd_1245736 : Nat := 426440891072962190580647

theorem tailTrace_1245736 : CollatzResearch.WordTrace tailWord_1245736 prefixEnd_1245736 426440891072962190580647 := by
  unfold tailWord_1245736
  simp only [CollatzResearch.WordTrace]
  refine ⟨22717862307459350807818531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30290483076612467743758041 22717862307459350807818531)
  ·
    refine ⟨34076793461189026211727797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22717862307459350807818531 34076793461189026211727797)
    ·
      refine ⟨3194699386986471207349481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34076793461189026211727797 3194699386986471207349481)
      ·
        refine ⟨2396024540239853405512111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3194699386986471207349481 2396024540239853405512111)
        ·
          refine ⟨3594036810359780108268167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2396024540239853405512111 3594036810359780108268167)
          ·
            refine ⟨5391055215539670162402251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3594036810359780108268167 5391055215539670162402251)
            ·
              refine ⟨8086582823309505243603377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5391055215539670162402251 8086582823309505243603377)
              ·
                refine ⟨6064937117482128932702533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8086582823309505243603377 6064937117482128932702533)
                ·
                  refine ⟨1137175709527899174881725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6064937117482128932702533 1137175709527899174881725)
                  ·
                    refine ⟨426440891072962190580647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1137175709527899174881725 426440891072962190580647)
                    ·
                      rfl

theorem cell22_1245736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_1245736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1245736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1245736 prefixEnd_1245736 := by exact prefixLift 1245736
  have htrace : WordTrace (prefixWord ++ tailWord_1245736) baseStart_1245736 baseEnd_1245736 := by
    simpa [prefixWord, tailWord_1245736, baseEnd_1245736] using wordTrace_append hprefix tailTrace_1245736
  have hstable : (prefixWord ++ tailWord_1245736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245736).length < 2 ^ (prefixWord ++ tailWord_1245736).sum := by decide
  have hdescent : baseEnd_1245736 < baseStart_1245736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245738 : List Nat := [3, 1, 4, 1, 1, 4, 1, 3, 4]
def baseStart_1245738 : Nat := 118140960795 + 1245738 * 2 ^ 59
def prefixEnd_1245738 : Nat := 4983230072969 + 3 ^ 40 * 1245738 * 2
def baseEnd_1245738 : Nat := 142147191904611617343547

theorem tailTrace_1245738 : CollatzResearch.WordTrace tailWord_1245738 prefixEnd_1245738 142147191904611617343547 := by
  unfold tailWord_1245738
  simp only [CollatzResearch.WordTrace]
  refine ⟨11358949390227863989302467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30290531707274303971473245 11358949390227863989302467)
  ·
    refine ⟨17038424085341795983953701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11358949390227863989302467 17038424085341795983953701)
    ·
      refine ⟨3194704516001586746991319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17038424085341795983953701 3194704516001586746991319)
      ·
        refine ⟨4792056774002380120486979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3194704516001586746991319 4792056774002380120486979)
        ·
          refine ⟨7188085161003570180730469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4792056774002380120486979 7188085161003570180730469)
          ·
            refine ⟨1347765967688169408886963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7188085161003570180730469 1347765967688169408886963)
            ·
              refine ⟨2021648951532254113330445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1347765967688169408886963 2021648951532254113330445)
              ·
                refine ⟨758118356824595292498917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2021648951532254113330445 758118356824595292498917)
                ·
                  refine ⟨142147191904611617343547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 758118356824595292498917 142147191904611617343547)
                  ·
                    rfl

theorem cell22_1245738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 3, 4].length) (baseStart_1245738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1245738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1245738 prefixEnd_1245738 := by exact prefixLift 1245738
  have htrace : WordTrace (prefixWord ++ tailWord_1245738) baseStart_1245738 baseEnd_1245738 := by
    simpa [prefixWord, tailWord_1245738, baseEnd_1245738] using wordTrace_append hprefix tailTrace_1245738
  have hstable : (prefixWord ++ tailWord_1245738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245738).length < 2 ^ (prefixWord ++ tailWord_1245738).sum := by decide
  have hdescent : baseEnd_1245738 < baseStart_1245738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245766 : List Nat := [6, 1, 1, 1, 2, 1, 1, 9]
def baseStart_1245766 : Nat := 118140960795 + 1245766 * 2 ^ 59
def prefixEnd_1245766 : Nat := 4983230072969 + 3 ^ 40 * 1245766 * 2
def baseEnd_1245766 : Nat := 47383462298450234703395

theorem tailTrace_1245766 : CollatzResearch.WordTrace tailWord_1245766 prefixEnd_1245766 47383462298450234703395 := by
  unfold tailWord_1245766
  simp only [CollatzResearch.WordTrace]
  refine ⟨1419900587650313023100911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30291212536540011159486101 1419900587650313023100911)
  ·
    refine ⟨2129850881475469534651367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1419900587650313023100911 2129850881475469534651367)
    ·
      refine ⟨3194776322213204301977051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2129850881475469534651367 3194776322213204301977051)
      ·
        refine ⟨4792164483319806452965577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3194776322213204301977051 4792164483319806452965577)
        ·
          refine ⟨3594123362489854839724183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4792164483319806452965577 3594123362489854839724183)
          ·
            refine ⟨5391185043734782259586275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3594123362489854839724183 5391185043734782259586275)
            ·
              refine ⟨8086777565602173389379413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5391185043734782259586275 8086777565602173389379413)
              ·
                refine ⟨47383462298450234703395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8086777565602173389379413 47383462298450234703395)
                ·
                  rfl

theorem cell22_1245766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_1245766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1245766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1245766 prefixEnd_1245766 := by exact prefixLift 1245766
  have htrace : WordTrace (prefixWord ++ tailWord_1245766) baseStart_1245766 baseEnd_1245766 := by
    simpa [prefixWord, tailWord_1245766, baseEnd_1245766] using wordTrace_append hprefix tailTrace_1245766
  have hstable : (prefixWord ++ tailWord_1245766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245766).length < 2 ^ (prefixWord ++ tailWord_1245766).sum := by decide
  have hdescent : baseEnd_1245766 < baseStart_1245766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245824 : List Nat := [2, 1, 1, 2, 1, 5, 1, 2, 3, 4]
def baseStart_1245824 : Nat := 118140960795 + 1245824 * 2 ^ 59
def prefixEnd_1245824 : Nat := 4983230072969 + 3 ^ 40 * 1245824 * 2
def baseEnd_1245824 : Nat := 426471015271359294380377

theorem tailTrace_1245824 : CollatzResearch.WordTrace tailWord_1245824 prefixEnd_1245824 426471015271359294380377 := by
  unfold tailWord_1245824
  simp only [CollatzResearch.WordTrace]
  refine ⟨22719467119299946322420263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30292622825733261763227017 22719467119299946322420263)
  ·
    refine ⟨34079200678949919483630395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22719467119299946322420263 34079200678949919483630395)
    ·
      refine ⟨51118801018424879225445593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34079200678949919483630395 51118801018424879225445593)
      ·
        refine ⟨38339100763818659419084195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51118801018424879225445593 38339100763818659419084195)
        ·
          refine ⟨57508651145727989128626293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38339100763818659419084195 57508651145727989128626293)
          ·
            refine ⟨5391436044911998980808715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57508651145727989128626293 5391436044911998980808715)
            ·
              refine ⟨8087154067367998471213073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5391436044911998980808715 8087154067367998471213073)
              ·
                refine ⟨6065365550525998853409805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8087154067367998471213073 6065365550525998853409805)
                ·
                  refine ⟨2274512081447249570028677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6065365550525998853409805 2274512081447249570028677)
                  ·
                    refine ⟨426471015271359294380377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2274512081447249570028677 426471015271359294380377)
                    ·
                      rfl

theorem cell22_1245824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 3, 4].length) (baseStart_1245824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1245824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1245824 prefixEnd_1245824 := by exact prefixLift 1245824
  have htrace : WordTrace (prefixWord ++ tailWord_1245824) baseStart_1245824 baseEnd_1245824 := by
    simpa [prefixWord, tailWord_1245824, baseEnd_1245824] using wordTrace_append hprefix tailTrace_1245824
  have hstable : (prefixWord ++ tailWord_1245824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245824).length < 2 ^ (prefixWord ++ tailWord_1245824).sum := by decide
  have hdescent : baseEnd_1245824 < baseStart_1245824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245871 : List Nat := [1, 1, 2, 1, 2, 6, 1, 1, 4, 3]
def baseStart_1245871 : Nat := 118140960795 + 1245871 * 2 ^ 59
def prefixEnd_1245871 : Nat := 4983230072969 + 3 ^ 40 * 1245871 * 2
def baseEnd_1245871 : Nat := 426487104331866838455233

theorem tailTrace_1245871 : CollatzResearch.WordTrace tailWord_1245871 prefixEnd_1245871 426487104331866838455233 := by
  unfold tailWord_1245871
  simp only [CollatzResearch.WordTrace]
  refine ⟨45440648469429619671801467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30293765646286413114534311 45440648469429619671801467)
  ·
    refine ⟨68160972704144429507702201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45440648469429619671801467 68160972704144429507702201)
    ·
      refine ⟨51120729528108322130776651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68160972704144429507702201 51120729528108322130776651)
      ·
        refine ⟨76681094292162483196164977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51120729528108322130776651 76681094292162483196164977)
        ·
          refine ⟨57510820719121862397123733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76681094292162483196164977 57510820719121862397123733)
          ·
            refine ⟨2695819721208837299865175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 57510820719121862397123733 2695819721208837299865175)
            ·
              refine ⟨4043729581813255949797763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2695819721208837299865175 4043729581813255949797763)
              ·
                refine ⟨6065594372719883924696645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4043729581813255949797763 6065594372719883924696645)
                ·
                  refine ⟨1137298944884978235880621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6065594372719883924696645 1137298944884978235880621)
                  ·
                    refine ⟨426487104331866838455233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1137298944884978235880621 426487104331866838455233)
                    ·
                      rfl

theorem cell22_1245871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 4, 3].length) (baseStart_1245871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1245871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1245871 prefixEnd_1245871 := by exact prefixLift 1245871
  have htrace : WordTrace (prefixWord ++ tailWord_1245871) baseStart_1245871 baseEnd_1245871 := by
    simpa [prefixWord, tailWord_1245871, baseEnd_1245871] using wordTrace_append hprefix tailTrace_1245871
  have hstable : (prefixWord ++ tailWord_1245871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245871).length < 2 ^ (prefixWord ++ tailWord_1245871).sum := by decide
  have hdescent : baseEnd_1245871 < baseStart_1245871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245873 : List Nat := [1, 2, 2, 6, 1, 1, 2, 1, 6]
def baseStart_1245873 : Nat := 118140960795 + 1245873 * 2 ^ 59
def prefixEnd_1245873 : Nat := 4983230072969 + 3 ^ 40 * 1245873 * 2
def baseEnd_1245873 : Nat := 142162596324246499968409

theorem tailTrace_1245873 : CollatzResearch.WordTrace tailWord_1245873 prefixEnd_1245873 142162596324246499968409 := by
  unfold tailWord_1245873
  simp only [CollatzResearch.WordTrace]
  refine ⟨45440721415422374013374273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30293814276948249342249515 45440721415422374013374273)
  ·
    refine ⟨34080541061566780510030705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45440721415422374013374273 34080541061566780510030705)
    ·
      refine ⟨25560405796175085382523029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34080541061566780510030705 25560405796175085382523029)
      ·
        refine ⟨1198144021695707127305767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25560405796175085382523029 1198144021695707127305767)
        ·
          refine ⟨1797216032543560690958651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1198144021695707127305767 1797216032543560690958651)
          ·
            refine ⟨2695824048815341036437977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1797216032543560690958651 2695824048815341036437977)
            ·
              refine ⟨2021868036611505777328483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2695824048815341036437977 2021868036611505777328483)
              ·
                refine ⟨3032802054917258665992725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2021868036611505777328483 3032802054917258665992725)
                ·
                  refine ⟨142162596324246499968409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3032802054917258665992725 142162596324246499968409)
                  ·
                    rfl

theorem cell22_1245873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 6].length) (baseStart_1245873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1245873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1245873 prefixEnd_1245873 := by exact prefixLift 1245873
  have htrace : WordTrace (prefixWord ++ tailWord_1245873) baseStart_1245873 baseEnd_1245873 := by
    simpa [prefixWord, tailWord_1245873, baseEnd_1245873] using wordTrace_append hprefix tailTrace_1245873
  have hstable : (prefixWord ++ tailWord_1245873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245873).length < 2 ^ (prefixWord ++ tailWord_1245873).sum := by decide
  have hdescent : baseEnd_1245873 < baseStart_1245873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245884 : List Nat := [2, 2, 2, 3, 1, 1, 2, 9]
def baseStart_1245884 : Nat := 118140960795 + 1245884 * 2 ^ 59
def prefixEnd_1245884 : Nat := 4983230072969 + 3 ^ 40 * 1245884 * 2
def baseEnd_1245884 : Nat := 47387950499726570875577

theorem tailTrace_1245884 : CollatzResearch.WordTrace tailWord_1245884 prefixEnd_1245884 47387950499726570875577 := by
  unfold tailWord_1245884
  simp only [CollatzResearch.WordTrace]
  refine ⟨22720561309191261446012353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30294081745588348594683137 22720561309191261446012353)
  ·
    refine ⟨17040420981893446084509265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22720561309191261446012353 17040420981893446084509265)
    ·
      refine ⟨12780315736420084563381949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17040420981893446084509265 12780315736420084563381949)
      ·
        refine ⟨4792618401157531711268231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12780315736420084563381949 4792618401157531711268231)
        ·
          refine ⟨7188927601736297566902347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4792618401157531711268231 7188927601736297566902347)
          ·
            refine ⟨10783391402604446350353521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7188927601736297566902347 10783391402604446350353521)
            ·
              refine ⟨8087543551953334762765141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10783391402604446350353521 8087543551953334762765141)
              ·
                refine ⟨47387950499726570875577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8087543551953334762765141 47387950499726570875577)
                ·
                  rfl

theorem cell22_1245884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 9].length) (baseStart_1245884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1245884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1245884 prefixEnd_1245884 := by exact prefixLift 1245884
  have htrace : WordTrace (prefixWord ++ tailWord_1245884) baseStart_1245884 baseEnd_1245884 := by
    simpa [prefixWord, tailWord_1245884, baseEnd_1245884] using wordTrace_append hprefix tailTrace_1245884
  have hstable : (prefixWord ++ tailWord_1245884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245884).length < 2 ^ (prefixWord ++ tailWord_1245884).sum := by decide
  have hdescent : baseEnd_1245884 < baseStart_1245884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245929 : List Nat := [1, 2, 1, 1, 1, 2, 6, 1, 7]
def baseStart_1245929 : Nat := 118140960795 + 1245929 * 2 ^ 59
def prefixEnd_1245929 : Nat := 4983230072969 + 3 ^ 40 * 1245929 * 2
def baseEnd_1245929 : Nat := 142168986305724673501685

theorem tailTrace_1245929 : CollatzResearch.WordTrace tailWord_1245929 prefixEnd_1245929 142168986305724673501685 := by
  unfold tailWord_1245929
  simp only [CollatzResearch.WordTrace]
  refine ⟨45442763903219495577412841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30295175935479663718275227 45442763903219495577412841)
  ·
    refine ⟨34082072927414621683059631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45442763903219495577412841 34082072927414621683059631)
    ·
      refine ⟨51123109391121932524589447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34082072927414621683059631 51123109391121932524589447)
      ·
        refine ⟨76684664086682898786884171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51123109391121932524589447 76684664086682898786884171)
        ·
          refine ⟨115026996130024348180326257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76684664086682898786884171 115026996130024348180326257)
          ·
            refine ⟨86270247097518261135244693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115026996130024348180326257 86270247097518261135244693)
            ·
              refine ⟨4043917832696168490714595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 86270247097518261135244693 4043917832696168490714595)
              ·
                refine ⟨6065876749044252736071893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4043917832696168490714595 6065876749044252736071893)
                ·
                  refine ⟨142168986305724673501685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6065876749044252736071893 142168986305724673501685)
                  ·
                    rfl

theorem cell22_1245929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 7].length) (baseStart_1245929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1245929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1245929 prefixEnd_1245929 := by exact prefixLift 1245929
  have htrace : WordTrace (prefixWord ++ tailWord_1245929) baseStart_1245929 baseEnd_1245929 := by
    simpa [prefixWord, tailWord_1245929, baseEnd_1245929] using wordTrace_append hprefix tailTrace_1245929
  have hstable : (prefixWord ++ tailWord_1245929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245929).length < 2 ^ (prefixWord ++ tailWord_1245929).sum := by decide
  have hdescent : baseEnd_1245929 < baseStart_1245929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245944 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 1, 7]
def baseStart_1245944 : Nat := 118140960795 + 1245944 * 2 ^ 59
def prefixEnd_1245944 : Nat := 4983230072969 + 3 ^ 40 * 1245944 * 2
def baseEnd_1245944 : Nat := 426512093723718981380009

theorem tailTrace_1245944 : CollatzResearch.WordTrace tailWord_1245944 prefixEnd_1245944 426512093723718981380009 := by
  unfold tailWord_1245944
  simp only [CollatzResearch.WordTrace]
  refine ⟨22721655499082576569604443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30295540665443435426139257 22721655499082576569604443)
  ·
    refine ⟨34082483248623864854406665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22721655499082576569604443 34082483248623864854406665)
    ·
      refine ⟨25561862436467898640804999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34082483248623864854406665 25561862436467898640804999)
      ·
        refine ⟨38342793654701847961207499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25561862436467898640804999 38342793654701847961207499)
        ·
          refine ⟨57514190482052771941811249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38342793654701847961207499 57514190482052771941811249)
          ·
            refine ⟨43135642861539578956358437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57514190482052771941811249 43135642861539578956358437)
            ·
              refine ⟨8087933036538671054317207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43135642861539578956358437 8087933036538671054317207)
              ·
                refine ⟨12131899554808006581475811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8087933036538671054317207 12131899554808006581475811)
                ·
                  refine ⟨18197849332212009872213717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12131899554808006581475811 18197849332212009872213717)
                  ·
                    refine ⟨426512093723718981380009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18197849332212009872213717 426512093723718981380009)
                    ·
                      rfl

theorem cell22_1245944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_1245944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1245944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1245944 prefixEnd_1245944 := by exact prefixLift 1245944
  have htrace : WordTrace (prefixWord ++ tailWord_1245944) baseStart_1245944 baseEnd_1245944 := by
    simpa [prefixWord, tailWord_1245944, baseEnd_1245944] using wordTrace_append hprefix tailTrace_1245944
  have hstable : (prefixWord ++ tailWord_1245944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245944).length < 2 ^ (prefixWord ++ tailWord_1245944).sum := by decide
  have hdescent : baseEnd_1245944 < baseStart_1245944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246021 : List Nat := [1, 3, 1, 1, 1, 2, 2, 5, 2, 4]
def baseStart_1246021 : Nat := 118140960795 + 1246021 * 2 ^ 59
def prefixEnd_1246021 : Nat := 4983230072969 + 3 ^ 40 * 1246021 * 2
def baseEnd_1246021 : Nat := 426538452397316447204773

theorem tailTrace_1246021 : CollatzResearch.WordTrace tailWord_1246021 prefixEnd_1246021 426538452397316447204773 := by
  unfold tailWord_1246021
  simp only [CollatzResearch.WordTrace]
  refine ⟨45446119418886195289761917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30297412945924130193174611 45446119418886195289761917)
  ·
    refine ⟨17042294782082323233660719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45446119418886195289761917 17042294782082323233660719)
    ·
      refine ⟨25563442173123484850491079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17042294782082323233660719 25563442173123484850491079)
      ·
        refine ⟨38345163259685227275736619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25563442173123484850491079 38345163259685227275736619)
        ·
          refine ⟨57517744889527840913604929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38345163259685227275736619 57517744889527840913604929)
          ·
            refine ⟨43138308667145880685203697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57517744889527840913604929 43138308667145880685203697)
            ·
              refine ⟨32353731500359410513902773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43138308667145880685203697 32353731500359410513902773)
              ·
                refine ⟨3033162328158694735678385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32353731500359410513902773 3033162328158694735678385)
                ·
                  refine ⟨2274871746119021051758789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3033162328158694735678385 2274871746119021051758789)
                  ·
                    refine ⟨426538452397316447204773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2274871746119021051758789 426538452397316447204773)
                    ·
                      rfl

theorem cell22_1246021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_1246021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246021 prefixEnd_1246021 := by exact prefixLift 1246021
  have htrace : WordTrace (prefixWord ++ tailWord_1246021) baseStart_1246021 baseEnd_1246021 := by
    simpa [prefixWord, tailWord_1246021, baseEnd_1246021] using wordTrace_append hprefix tailTrace_1246021
  have hstable : (prefixWord ++ tailWord_1246021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246021).length < 2 ^ (prefixWord ++ tailWord_1246021).sum := by decide
  have hdescent : baseEnd_1246021 < baseStart_1246021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246066 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 2, 6]
def baseStart_1246066 : Nat := 118140960795 + 1246066 * 2 ^ 59
def prefixEnd_1246066 : Nat := 4983230072969 + 3 ^ 40 * 1246066 * 2
def baseEnd_1246066 : Nat := 426553856816951329829635

theorem tailTrace_1246066 : CollatzResearch.WordTrace tailWord_1246066 prefixEnd_1246066 426553856816951329829635 := by
  unfold tailWord_1246066
  simp only [CollatzResearch.WordTrace]
  refine ⟨11361940175930791993787513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30298507135815445316766701 11361940175930791993787513)
  ·
    refine ⟨8521455131948093995340635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11361940175930791993787513 8521455131948093995340635)
    ·
      refine ⟨12782182697922140993010953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8521455131948093995340635 12782182697922140993010953)
      ·
        refine ⟨9586637023441605744758215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12782182697922140993010953 9586637023441605744758215)
        ·
          refine ⟨14379955535162408617137323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9586637023441605744758215 14379955535162408617137323)
          ·
            refine ⟨21569933302743612925705985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14379955535162408617137323 21569933302743612925705985)
            ·
              refine ⟨16177449977057709694279489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21569933302743612925705985 16177449977057709694279489)
              ·
                refine ⟨12133087482793282270709617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16177449977057709694279489 12133087482793282270709617)
                ·
                  refine ⟨9099815612094961703032213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12133087482793282270709617 9099815612094961703032213)
                  ·
                    refine ⟨426553856816951329829635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9099815612094961703032213 426553856816951329829635)
                    ·
                      rfl

theorem cell22_1246066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_1246066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246066 prefixEnd_1246066 := by exact prefixLift 1246066
  have htrace : WordTrace (prefixWord ++ tailWord_1246066) baseStart_1246066 baseEnd_1246066 := by
    simpa [prefixWord, tailWord_1246066, baseEnd_1246066] using wordTrace_append hprefix tailTrace_1246066
  have hstable : (prefixWord ++ tailWord_1246066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246066).length < 2 ^ (prefixWord ++ tailWord_1246066).sum := by decide
  have hdescent : baseEnd_1246066 < baseStart_1246066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246070 : List Nat := [5, 1, 1, 3, 1, 1, 4, 6]
def baseStart_1246070 : Nat := 118140960795 + 1246070 * 2 ^ 59
def prefixEnd_1246070 : Nat := 4983230072969 + 3 ^ 40 * 1246070 * 2
def baseEnd_1246070 : Nat := 47395025122077405858847

theorem tailTrace_1246070 : CollatzResearch.WordTrace tailWord_1246070 prefixEnd_1246070 47395025122077405858847 := by
  unfold tailWord_1246070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2840494162231792291143479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30298604397139117772197109 2840494162231792291143479)
  ·
    refine ⟨4260741243347688436715219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2840494162231792291143479 4260741243347688436715219)
    ·
      refine ⟨6391111865021532655072829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4260741243347688436715219 6391111865021532655072829)
      ·
        refine ⟨2396666949383074745652311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6391111865021532655072829 2396666949383074745652311)
        ·
          refine ⟨3595000424074612118478467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2396666949383074745652311 3595000424074612118478467)
          ·
            refine ⟨5392500636111918177717701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3595000424074612118478467 5392500636111918177717701)
            ·
              refine ⟨1011093869270984658322069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5392500636111918177717701 1011093869270984658322069)
              ·
                refine ⟨47395025122077405858847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1011093869270984658322069 47395025122077405858847)
                ·
                  rfl

theorem cell22_1246070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_1246070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246070 prefixEnd_1246070 := by exact prefixLift 1246070
  have htrace : WordTrace (prefixWord ++ tailWord_1246070) baseStart_1246070 baseEnd_1246070 := by
    simpa [prefixWord, tailWord_1246070, baseEnd_1246070] using wordTrace_append hprefix tailTrace_1246070
  have hstable : (prefixWord ++ tailWord_1246070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246070).length < 2 ^ (prefixWord ++ tailWord_1246070).sum := by decide
  have hdescent : baseEnd_1246070 < baseStart_1246070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246175 : List Nat := [1, 1, 2, 3, 5, 1, 2, 1, 1, 5]
def baseStart_1246175 : Nat := 118140960795 + 1246175 * 2 ^ 59
def prefixEnd_1246175 : Nat := 4983230072969 + 3 ^ 40 * 1246175 * 2
def baseEnd_1246175 : Nat := 426591169744511378854301

theorem tailTrace_1246175 : CollatzResearch.WordTrace tailWord_1246175 prefixEnd_1246175 426591169744511378854301 := by
  unfold tailWord_1246175
  simp only [CollatzResearch.WordTrace]
  refine ⟨45451736260328279590867979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30301157506885519727245319 45451736260328279590867979)
  ·
    refine ⟨68177604390492419386301969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45451736260328279590867979 68177604390492419386301969)
    ·
      refine ⟨51133203292869314539726477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68177604390492419386301969 51133203292869314539726477)
      ·
        refine ⟨19174951234825992952397429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51133203292869314539726477 19174951234825992952397429)
        ·
          refine ⟨1797651678264936839287259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19174951234825992952397429 1797651678264936839287259)
          ·
            refine ⟨2696477517397405258930889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1797651678264936839287259 2696477517397405258930889)
            ·
              refine ⟨2022358138048053944198167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2696477517397405258930889 2022358138048053944198167)
              ·
                refine ⟨3033537207072080916297251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2022358138048053944198167 3033537207072080916297251)
                ·
                  refine ⟨4550305810608121374445877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3033537207072080916297251 4550305810608121374445877)
                  ·
                    refine ⟨426591169744511378854301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4550305810608121374445877 426591169744511378854301)
                    ·
                      rfl

theorem cell22_1246175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 5].length) (baseStart_1246175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246175 prefixEnd_1246175 := by exact prefixLift 1246175
  have htrace : WordTrace (prefixWord ++ tailWord_1246175) baseStart_1246175 baseEnd_1246175 := by
    simpa [prefixWord, tailWord_1246175, baseEnd_1246175] using wordTrace_append hprefix tailTrace_1246175
  have hstable : (prefixWord ++ tailWord_1246175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246175).length < 2 ^ (prefixWord ++ tailWord_1246175).sum := by decide
  have hdescent : baseEnd_1246175 < baseStart_1246175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246190 : List Nat := [4, 1, 2, 1, 4, 1, 1, 1, 1, 6]
def baseStart_1246190 : Nat := 118140960795 + 1246190 * 2 ^ 59
def prefixEnd_1246190 : Nat := 4983230072969 + 3 ^ 40 * 1246190 * 2
def baseEnd_1246190 : Nat := 426596304551056339729255

theorem tailTrace_1246190 : CollatzResearch.WordTrace tailWord_1246190 prefixEnd_1246190 426596304551056339729255 := by
  unfold tailWord_1246190
  simp only [CollatzResearch.WordTrace]
  refine ⟨5681535419409242144083003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30301522236849291435109349 5681535419409242144083003)
  ·
    refine ⟨8522303129113863216124505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5681535419409242144083003 8522303129113863216124505)
    ·
      refine ⟨6391727346835397412093379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8522303129113863216124505 6391727346835397412093379)
      ·
        refine ⟨9587591020253096118140069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6391727346835397412093379 9587591020253096118140069)
        ·
          refine ⟨1797673316297455522151263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9587591020253096118140069 1797673316297455522151263)
          ·
            refine ⟨2696509974446183283226895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1797673316297455522151263 2696509974446183283226895)
            ·
              refine ⟨4044764961669274924840343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2696509974446183283226895 4044764961669274924840343)
              ·
                refine ⟨6067147442503912387260515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4044764961669274924840343 6067147442503912387260515)
                ·
                  refine ⟨9100721163755868580890773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6067147442503912387260515 9100721163755868580890773)
                  ·
                    refine ⟨426596304551056339729255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9100721163755868580890773 426596304551056339729255)
                    ·
                      rfl

theorem cell22_1246190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_1246190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246190 prefixEnd_1246190 := by exact prefixLift 1246190
  have htrace : WordTrace (prefixWord ++ tailWord_1246190) baseStart_1246190 baseEnd_1246190 := by
    simpa [prefixWord, tailWord_1246190, baseEnd_1246190] using wordTrace_append hprefix tailTrace_1246190
  have hstable : (prefixWord ++ tailWord_1246190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246190).length < 2 ^ (prefixWord ++ tailWord_1246190).sum := by decide
  have hdescent : baseEnd_1246190 < baseStart_1246190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246194 : List Nat := [3, 2, 1, 5, 1, 1, 2, 3, 4]
def baseStart_1246194 : Nat := 118140960795 + 1246194 * 2 ^ 59
def prefixEnd_1246194 : Nat := 4983230072969 + 3 ^ 40 * 1246194 * 2
def baseEnd_1246194 : Nat := 142199224610933887543081

theorem tailTrace_1246194 : CollatzResearch.WordTrace tailWord_1246194 prefixEnd_1246194 142199224610933887543081 := by
  unfold tailWord_1246194
  simp only [CollatzResearch.WordTrace]
  refine ⟨11363107311814861458952409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30301619498172963890539757 11363107311814861458952409)
  ·
    refine ⟨8522330483861146094214307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11363107311814861458952409 8522330483861146094214307)
    ·
      refine ⟨12783495725791719141321461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8522330483861146094214307 12783495725791719141321461)
      ·
        refine ⟨1198452724292973669498887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12783495725791719141321461 1198452724292973669498887)
        ·
          refine ⟨1797679086439460504248331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1198452724292973669498887 1797679086439460504248331)
          ·
            refine ⟨2696518629659190756372497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1797679086439460504248331 2696518629659190756372497)
            ·
              refine ⟨2022388972244393067279373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2696518629659190756372497 2022388972244393067279373)
              ·
                refine ⟨758395864591647400229765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2022388972244393067279373 758395864591647400229765)
                ·
                  refine ⟨142199224610933887543081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 758395864591647400229765 142199224610933887543081)
                  ·
                    rfl

theorem cell22_1246194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_1246194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246194 prefixEnd_1246194 := by exact prefixLift 1246194
  have htrace : WordTrace (prefixWord ++ tailWord_1246194) baseStart_1246194 baseEnd_1246194 := by
    simpa [prefixWord, tailWord_1246194, baseEnd_1246194] using wordTrace_append hprefix tailTrace_1246194
  have hstable : (prefixWord ++ tailWord_1246194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246194).length < 2 ^ (prefixWord ++ tailWord_1246194).sum := by decide
  have hdescent : baseEnd_1246194 < baseStart_1246194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246203 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 7, 3]
def baseStart_1246203 : Nat := 118140960795 + 1246203 * 2 ^ 59
def prefixEnd_1246203 : Nat := 4983230072969 + 3 ^ 40 * 1246203 * 2
def baseEnd_1246203 : Nat := 426600754716728639154215

theorem tailTrace_1246203 : CollatzResearch.WordTrace tailWord_1246203 prefixEnd_1246203 426600754716728639154215 := by
  unfold tailWord_1246203
  simp only [CollatzResearch.WordTrace]
  refine ⟨45452757504226840372887263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30301838336151226915258175 45452757504226840372887263)
  ·
    refine ⟨68179136256340260559330895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45452757504226840372887263 68179136256340260559330895)
    ·
      refine ⟨102268704384510390838996343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68179136256340260559330895 102268704384510390838996343)
      ·
        refine ⟨153403056576765586258494515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102268704384510390838996343 153403056576765586258494515)
        ·
          refine ⟨230104584865148379387741773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153403056576765586258494515 230104584865148379387741773)
          ·
            refine ⟨86289219324430642270403165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 230104584865148379387741773 86289219324430642270403165)
            ·
              refine ⟨32358457246661490851401187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86289219324430642270403165 32358457246661490851401187)
              ·
                refine ⟨48537685869992236277101781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32358457246661490851401187 48537685869992236277101781)
                ·
                  refine ⟨1137602012577943037744573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 48537685869992236277101781 1137602012577943037744573)
                  ·
                    refine ⟨426600754716728639154215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1137602012577943037744573 426600754716728639154215)
                    ·
                      rfl

theorem cell22_1246203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 7, 3].length) (baseStart_1246203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246203 prefixEnd_1246203 := by exact prefixLift 1246203
  have htrace : WordTrace (prefixWord ++ tailWord_1246203) baseStart_1246203 baseEnd_1246203 := by
    simpa [prefixWord, tailWord_1246203, baseEnd_1246203] using wordTrace_append hprefix tailTrace_1246203
  have hstable : (prefixWord ++ tailWord_1246203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246203).length < 2 ^ (prefixWord ++ tailWord_1246203).sum := by decide
  have hdescent : baseEnd_1246203 < baseStart_1246203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246220 : List Nat := [2, 2, 1, 2, 3, 2, 1, 3, 3, 3]
def baseStart_1246220 : Nat := 118140960795 + 1246220 * 2 ^ 59
def prefixEnd_1246220 : Nat := 4983230072969 + 3 ^ 40 * 1246220 * 2
def baseEnd_1246220 : Nat := 426606574164146261479163

theorem tailTrace_1246220 : CollatzResearch.WordTrace tailWord_1246220 prefixEnd_1246220 426606574164146261479163 := by
  unfold tailWord_1246220
  simp only [CollatzResearch.WordTrace]
  refine ⟨22726688772582626138128057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30302251696776834850837409 22726688772582626138128057)
  ·
    refine ⟨17045016579436969603596043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22726688772582626138128057 17045016579436969603596043)
    ·
      refine ⟨25567524869155454405394065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17045016579436969603596043 25567524869155454405394065)
      ·
        refine ⟨19175643651866590804045549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25567524869155454405394065 19175643651866590804045549)
        ·
          refine ⟨7190866369449971551517081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19175643651866590804045549 7190866369449971551517081)
          ·
            refine ⟨5393149777087478663637811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7190866369449971551517081 5393149777087478663637811)
            ·
              refine ⟨8089724665631217995456717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5393149777087478663637811 8089724665631217995456717)
              ·
                refine ⟨3033646749611706748296269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8089724665631217995456717 3033646749611706748296269)
                ·
                  refine ⟨1137617531104390030611101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3033646749611706748296269 1137617531104390030611101)
                  ·
                    refine ⟨426606574164146261479163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1137617531104390030611101 426606574164146261479163)
                    ·
                      rfl

theorem cell22_1246220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 3, 3].length) (baseStart_1246220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246220 prefixEnd_1246220 := by exact prefixLift 1246220
  have htrace : WordTrace (prefixWord ++ tailWord_1246220) baseStart_1246220 baseEnd_1246220 := by
    simpa [prefixWord, tailWord_1246220, baseEnd_1246220] using wordTrace_append hprefix tailTrace_1246220
  have hstable : (prefixWord ++ tailWord_1246220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246220).length < 2 ^ (prefixWord ++ tailWord_1246220).sum := by decide
  have hdescent : baseEnd_1246220 < baseStart_1246220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246226 : List Nat := [3, 2, 5, 1, 1, 2, 1, 1, 1, 5]
def baseStart_1246226 : Nat := 118140960795 + 1246226 * 2 ^ 59
def prefixEnd_1246226 : Nat := 4983230072969 + 3 ^ 40 * 1246226 * 2
def baseEnd_1246226 : Nat := 426608628086764245829145

theorem tailTrace_1246226 : CollatzResearch.WordTrace tailWord_1246226 prefixEnd_1246226 426608628086764245829145 := by
  unfold tailWord_1246226
  simp only [CollatzResearch.WordTrace]
  refine ⟨11363399095785878825243633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30302397588762343533983021 11363399095785878825243633)
  ·
    refine ⟨8522549321839409118932725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11363399095785878825243633 8522549321839409118932725)
    ·
      refine ⟨798988998922444604899943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8522549321839409118932725 798988998922444604899943)
      ·
        refine ⟨1198483498383666907349915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 798988998922444604899943 1198483498383666907349915)
        ·
          refine ⟨1797725247575500361024873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1198483498383666907349915 1797725247575500361024873)
          ·
            refine ⟨1348293935681625270768655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1797725247575500361024873 1348293935681625270768655)
            ·
              refine ⟨2022440903522437906152983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1348293935681625270768655 2022440903522437906152983)
              ·
                refine ⟨3033661355283656859229475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2022440903522437906152983 3033661355283656859229475)
                ·
                  refine ⟨4550492032925485288844213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3033661355283656859229475 4550492032925485288844213)
                  ·
                    refine ⟨426608628086764245829145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4550492032925485288844213 426608628086764245829145)
                    ·
                      rfl

theorem cell22_1246226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_1246226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246226 prefixEnd_1246226 := by exact prefixLift 1246226
  have htrace : WordTrace (prefixWord ++ tailWord_1246226) baseStart_1246226 baseEnd_1246226 := by
    simpa [prefixWord, tailWord_1246226, baseEnd_1246226] using wordTrace_append hprefix tailTrace_1246226
  have hstable : (prefixWord ++ tailWord_1246226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246226).length < 2 ^ (prefixWord ++ tailWord_1246226).sum := by decide
  have hdescent : baseEnd_1246226 < baseStart_1246226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246233 : List Nat := [1, 2, 1, 2, 1, 1, 4, 5, 5]
def baseStart_1246233 : Nat := 118140960795 + 1246233 * 2 ^ 59
def prefixEnd_1246233 : Nat := 4983230072969 + 3 ^ 40 * 1246233 * 2
def baseEnd_1246233 : Nat := 142203674776606186968041

theorem tailTrace_1246233 : CollatzResearch.WordTrace tailWord_1246233 prefixEnd_1246233 142203674776606186968041 := by
  unfold tailWord_1246233
  simp only [CollatzResearch.WordTrace]
  refine ⟨45453851694118155496479353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30302567796078770330986235 45453851694118155496479353)
  ·
    refine ⟨34090388770588616622359515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45453851694118155496479353 34090388770588616622359515)
    ·
      refine ⟨51135583155882924933539273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34090388770588616622359515 51135583155882924933539273)
      ·
        refine ⟨38351687366912193700154455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51135583155882924933539273 38351687366912193700154455)
        ·
          refine ⟨57527531050368290550231683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38351687366912193700154455 57527531050368290550231683)
          ·
            refine ⟨86291296575552435825347525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57527531050368290550231683 86291296575552435825347525)
            ·
              refine ⟨16179618107916081717252661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86291296575552435825347525 16179618107916081717252661)
              ·
                refine ⟨1516839197617132660992437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16179618107916081717252661 1516839197617132660992437)
                ·
                  refine ⟨142203674776606186968041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1516839197617132660992437 142203674776606186968041)
                  ·
                    rfl

theorem cell22_1246233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 5].length) (baseStart_1246233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246233 prefixEnd_1246233 := by exact prefixLift 1246233
  have htrace : WordTrace (prefixWord ++ tailWord_1246233) baseStart_1246233 baseEnd_1246233 := by
    simpa [prefixWord, tailWord_1246233, baseEnd_1246233] using wordTrace_append hprefix tailTrace_1246233
  have hstable : (prefixWord ++ tailWord_1246233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246233).length < 2 ^ (prefixWord ++ tailWord_1246233).sum := by decide
  have hdescent : baseEnd_1246233 < baseStart_1246233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246263 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 5, 4]
def baseStart_1246263 : Nat := 118140960795 + 1246263 * 2 ^ 59
def prefixEnd_1246263 : Nat := 4983230072969 + 3 ^ 40 * 1246263 * 2
def baseEnd_1246263 : Nat := 426621293942908482654031

theorem tailTrace_1246263 : CollatzResearch.WordTrace tailWord_1246263 prefixEnd_1246263 426621293942908482654031 := by
  unfold tailWord_1246263
  simp only [CollatzResearch.WordTrace]
  refine ⟨45454945884009470620071443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30303297256006313746714295 45454945884009470620071443)
  ·
    refine ⟨68182418826014205930107165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45454945884009470620071443 68182418826014205930107165)
    ·
      refine ⟨25568407059755327223790187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68182418826014205930107165 25568407059755327223790187)
      ·
        refine ⟨38352610589632990835685281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25568407059755327223790187 38352610589632990835685281)
        ·
          refine ⟨28764457942224743126763961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38352610589632990835685281 28764457942224743126763961)
          ·
            refine ⟨21573343456668557345072971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28764457942224743126763961 21573343456668557345072971)
            ·
              refine ⟨32360015185002836017609457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21573343456668557345072971 32360015185002836017609457)
              ·
                refine ⟨24270011388752127013207093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32360015185002836017609457 24270011388752127013207093)
                ·
                  refine ⟨2275313567695511907488165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24270011388752127013207093 2275313567695511907488165)
                  ·
                    refine ⟨426621293942908482654031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2275313567695511907488165 426621293942908482654031)
                    ·
                      rfl

theorem cell22_1246263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_1246263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246263 prefixEnd_1246263 := by exact prefixLift 1246263
  have htrace : WordTrace (prefixWord ++ tailWord_1246263) baseStart_1246263 baseEnd_1246263 := by
    simpa [prefixWord, tailWord_1246263, baseEnd_1246263] using wordTrace_append hprefix tailTrace_1246263
  have hstable : (prefixWord ++ tailWord_1246263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246263).length < 2 ^ (prefixWord ++ tailWord_1246263).sum := by decide
  have hdescent : baseEnd_1246263 < baseStart_1246263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246314 : List Nat := [3, 1, 3, 2, 2, 2, 3, 1, 1, 4]
def baseStart_1246314 : Nat := 118140960795 + 1246314 * 2 ^ 59
def prefixEnd_1246314 : Nat := 4983230072969 + 3 ^ 40 * 1246314 * 2
def baseEnd_1246314 : Nat := 426638752285161349628875

theorem tailTrace_1246314 : CollatzResearch.WordTrace tailWord_1246314 prefixEnd_1246314 426638752285161349628875 := by
  unfold tailWord_1246314
  simp only [CollatzResearch.WordTrace]
  refine ⟨11364201501706176582544499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30304537337883137553451997 11364201501706176582544499)
  ·
    refine ⟨17046302252559264873816749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11364201501706176582544499 17046302252559264873816749)
    ·
      refine ⟨6392363344709724327681281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17046302252559264873816749 6392363344709724327681281)
      ·
        refine ⟨4794272508532293245760961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6392363344709724327681281 4794272508532293245760961)
        ·
          refine ⟨3595704381399219934320721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4794272508532293245760961 3595704381399219934320721)
          ·
            refine ⟨2696778286049414950740541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3595704381399219934320721 2696778286049414950740541)
            ·
              refine ⟨1011291857268530606527703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2696778286049414950740541 1011291857268530606527703)
              ·
                refine ⟨1516937785902795909791555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1011291857268530606527703 1516937785902795909791555)
                ·
                  refine ⟨2275406678854193864687333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1516937785902795909791555 2275406678854193864687333)
                  ·
                    refine ⟨426638752285161349628875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2275406678854193864687333 426638752285161349628875)
                    ·
                      rfl

theorem cell22_1246314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_1246314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246314 prefixEnd_1246314 := by exact prefixLift 1246314
  have htrace : WordTrace (prefixWord ++ tailWord_1246314) baseStart_1246314 baseEnd_1246314 := by
    simpa [prefixWord, tailWord_1246314, baseEnd_1246314] using wordTrace_append hprefix tailTrace_1246314
  have hstable : (prefixWord ++ tailWord_1246314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246314).length < 2 ^ (prefixWord ++ tailWord_1246314).sum := by decide
  have hdescent : baseEnd_1246314 < baseStart_1246314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246327 : List Nat := [1, 1, 3, 1, 1, 4, 4, 2, 2, 3]
def baseStart_1246327 : Nat := 118140960795 + 1246327 * 2 ^ 59
def prefixEnd_1246327 : Nat := 4983230072969 + 3 ^ 40 * 1246327 * 2
def baseEnd_1246327 : Nat := 426643202450833649053835

theorem tailTrace_1246327 : CollatzResearch.WordTrace tailWord_1246327 prefixEnd_1246327 426643202450833649053835 := by
  unfold tailWord_1246327
  simp only [CollatzResearch.WordTrace]
  refine ⟨45457280155777609550401235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30304853437185073033600823 45457280155777609550401235)
  ·
    refine ⟨68185920233666414325601853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45457280155777609550401235 68185920233666414325601853)
    ·
      refine ⟨25569720087624905372100695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68185920233666414325601853 25569720087624905372100695)
      ·
        refine ⟨38354580131437358058151043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25569720087624905372100695 38354580131437358058151043)
        ·
          refine ⟨57531870197156037087226565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38354580131437358058151043 57531870197156037087226565)
          ·
            refine ⟨10787225661966756953854981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57531870197156037087226565 10787225661966756953854981)
            ·
              refine ⟨2022604811618766928847809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10787225661966756953854981 2022604811618766928847809)
              ·
                refine ⟨1516953608714075196635857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2022604811618766928847809 1516953608714075196635857)
                ·
                  refine ⟨1137715206535556397476893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1516953608714075196635857 1137715206535556397476893)
                  ·
                    refine ⟨426643202450833649053835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1137715206535556397476893 426643202450833649053835)
                    ·
                      rfl

theorem cell22_1246327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 2, 3].length) (baseStart_1246327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246327 prefixEnd_1246327 := by exact prefixLift 1246327
  have htrace : WordTrace (prefixWord ++ tailWord_1246327) baseStart_1246327 baseEnd_1246327 := by
    simpa [prefixWord, tailWord_1246327, baseEnd_1246327] using wordTrace_append hprefix tailTrace_1246327
  have hstable : (prefixWord ++ tailWord_1246327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246327).length < 2 ^ (prefixWord ++ tailWord_1246327).sum := by decide
  have hdescent : baseEnd_1246327 < baseStart_1246327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246340 : List Nat := [2, 3, 2, 1, 2, 2, 3, 7]
def baseStart_1246340 : Nat := 118140960795 + 1246340 * 2 ^ 59
def prefixEnd_1246340 : Nat := 4983230072969 + 3 ^ 40 * 1246340 * 2
def baseEnd_1246340 : Nat := 47405294735167327608755

theorem tailTrace_1246340 : CollatzResearch.WordTrace tailWord_1246340 prefixEnd_1246340 47405294735167327608755 := by
  unfold tailWord_1246340
  simp only [CollatzResearch.WordTrace]
  refine ⟨22728877152365256385312237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30305169536487008513749649 22728877152365256385312237)
  ·
    refine ⟨8523328932136971144492089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22728877152365256385312237 8523328932136971144492089)
    ·
      refine ⟨6392496699102728358369067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8523328932136971144492089 6392496699102728358369067)
      ·
        refine ⟨9588745048654092537553601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6392496699102728358369067 9588745048654092537553601)
        ·
          refine ⟨7191558786490569403165201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9588745048654092537553601 7191558786490569403165201)
          ·
            refine ⟨5393669089867927052373901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7191558786490569403165201 5393669089867927052373901)
            ·
              refine ⟨2022625908700472644640213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5393669089867927052373901 2022625908700472644640213)
              ·
                refine ⟨47405294735167327608755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2022625908700472644640213 47405294735167327608755)
                ·
                  rfl

theorem cell22_1246340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 7].length) (baseStart_1246340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246340 prefixEnd_1246340 := by exact prefixLift 1246340
  have htrace : WordTrace (prefixWord ++ tailWord_1246340) baseStart_1246340 baseEnd_1246340 := by
    simpa [prefixWord, tailWord_1246340, baseEnd_1246340] using wordTrace_append hprefix tailTrace_1246340
  have hstable : (prefixWord ++ tailWord_1246340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246340).length < 2 ^ (prefixWord ++ tailWord_1246340).sum := by decide
  have hdescent : baseEnd_1246340 < baseStart_1246340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246355 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 5, 3]
def baseStart_1246355 : Nat := 118140960795 + 1246355 * 2 ^ 59
def prefixEnd_1246355 : Nat := 4983230072969 + 3 ^ 40 * 1246355 * 2
def baseEnd_1246355 : Nat := 426652787423050909353749

theorem tailTrace_1246355 : CollatzResearch.WordTrace tailWord_1246355 prefixEnd_1246355 426652787423050909353749 := by
  unfold tailWord_1246355
  simp only [CollatzResearch.WordTrace]
  refine ⟨45458301399676170332420519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30305534266450780221613679 45458301399676170332420519)
  ·
    refine ⟨68187452099514255498630779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45458301399676170332420519 68187452099514255498630779)
    ·
      refine ⟨102281178149271383247946169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68187452099514255498630779 102281178149271383247946169)
      ·
        refine ⟨76710883611953537435959627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102281178149271383247946169 76710883611953537435959627)
        ·
          refine ⟨115066325417930306153939441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76710883611953537435959627 115066325417930306153939441)
          ·
            refine ⟨86299744063447729615454581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115066325417930306153939441 86299744063447729615454581)
            ·
              refine ⟨8090601005948224651448867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86299744063447729615454581 8090601005948224651448867)
              ·
                refine ⟨12135901508922336977173301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8090601005948224651448867 12135901508922336977173301)
                ·
                  refine ⟨1137740766461469091609997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12135901508922336977173301 1137740766461469091609997)
                  ·
                    refine ⟨426652787423050909353749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1137740766461469091609997 426652787423050909353749)
                    ·
                      rfl

theorem cell22_1246355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 5, 3].length) (baseStart_1246355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246355 prefixEnd_1246355 := by exact prefixLift 1246355
  have htrace : WordTrace (prefixWord ++ tailWord_1246355) baseStart_1246355 baseEnd_1246355 := by
    simpa [prefixWord, tailWord_1246355, baseEnd_1246355] using wordTrace_append hprefix tailTrace_1246355
  have hstable : (prefixWord ++ tailWord_1246355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246355).length < 2 ^ (prefixWord ++ tailWord_1246355).sum := by decide
  have hdescent : baseEnd_1246355 < baseStart_1246355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246432 : List Nat := [2, 1, 1, 3, 1, 4, 2, 3, 1, 4]
def baseStart_1246432 : Nat := 118140960795 + 1246432 * 2 ^ 59
def prefixEnd_1246432 : Nat := 4983230072969 + 3 ^ 40 * 1246432 * 2
def baseEnd_1246432 : Nat := 426679146096648375178513

theorem tailTrace_1246432 : CollatzResearch.WordTrace tailWord_1246432 prefixEnd_1246432 426679146096648375178513 := by
  unfold tailWord_1246432
  simp only [CollatzResearch.WordTrace]
  refine ⟨22730554910198606241486775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30307406546931474988649033 22730554910198606241486775)
  ·
    refine ⟨34095832365297909362230163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22730554910198606241486775 34095832365297909362230163)
    ·
      refine ⟨51143748547946864043345245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34095832365297909362230163 51143748547946864043345245)
      ·
        refine ⟨19178905705480074016254467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51143748547946864043345245 19178905705480074016254467)
        ·
          refine ⟨28768358558220111024381701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19178905705480074016254467 28768358558220111024381701)
          ·
            refine ⟨5394067229666270817071569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28768358558220111024381701 5394067229666270817071569)
            ·
              refine ⟨4045550422249703112803677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5394067229666270817071569 4045550422249703112803677)
              ·
                refine ⟨1517081408343638667301379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4045550422249703112803677 1517081408343638667301379)
                ·
                  refine ⟨2275622112515458000952069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1517081408343638667301379 2275622112515458000952069)
                  ·
                    refine ⟨426679146096648375178513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2275622112515458000952069 426679146096648375178513)
                    ·
                      rfl

theorem cell22_1246432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 1, 4].length) (baseStart_1246432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246432 prefixEnd_1246432 := by exact prefixLift 1246432
  have htrace : WordTrace (prefixWord ++ tailWord_1246432) baseStart_1246432 baseEnd_1246432 := by
    simpa [prefixWord, tailWord_1246432, baseEnd_1246432] using wordTrace_append hprefix tailTrace_1246432
  have hstable : (prefixWord ++ tailWord_1246432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246432).length < 2 ^ (prefixWord ++ tailWord_1246432).sum := by decide
  have hdescent : baseEnd_1246432 < baseStart_1246432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246475 : List Nat := [1, 1, 1, 1, 5, 3, 2, 8]
def baseStart_1246475 : Nat := 118140960795 + 1246475 * 2 ^ 59
def prefixEnd_1246475 : Nat := 4983230072969 + 3 ^ 40 * 1246475 * 2
def baseEnd_1246475 : Nat := 47410429541712288483709

theorem tailTrace_1246475 : CollatzResearch.WordTrace tailWord_1246475 prefixEnd_1246475 47410429541712288483709 := by
  unfold tailWord_1246475
  simp only [CollatzResearch.WordTrace]
  refine ⟨45462678159241430826788879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30308452106160953884525919 45462678159241430826788879)
  ·
    refine ⟨68194017238862146240183319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45462678159241430826788879 68194017238862146240183319)
    ·
      refine ⟨102291025858293219360274979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68194017238862146240183319 102291025858293219360274979)
      ·
        refine ⟨153436538787439829040412469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102291025858293219360274979 153436538787439829040412469)
        ·
          refine ⟨14384675511322483972538669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 153436538787439829040412469 14384675511322483972538669)
          ·
            refine ⟨5394253316745931489702001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14384675511322483972538669 5394253316745931489702001)
            ·
              refine ⟨4045689987559448617276501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5394253316745931489702001 4045689987559448617276501)
              ·
                refine ⟨47410429541712288483709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4045689987559448617276501 47410429541712288483709)
                ·
                  rfl

theorem cell22_1246475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 8].length) (baseStart_1246475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246475 prefixEnd_1246475 := by exact prefixLift 1246475
  have htrace : WordTrace (prefixWord ++ tailWord_1246475) baseStart_1246475 baseEnd_1246475 := by
    simpa [prefixWord, tailWord_1246475, baseEnd_1246475] using wordTrace_append hprefix tailTrace_1246475
  have hstable : (prefixWord ++ tailWord_1246475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246475).length < 2 ^ (prefixWord ++ tailWord_1246475).sum := by decide
  have hdescent : baseEnd_1246475 < baseStart_1246475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246496 : List Nat := [2, 1, 1, 5, 3, 1, 2, 2, 2, 3]
def baseStart_1246496 : Nat := 118140960795 + 1246496 * 2 ^ 59
def prefixEnd_1246496 : Nat := 4983230072969 + 3 ^ 40 * 1246496 * 2
def baseEnd_1246496 : Nat := 426701054604573541578317

theorem tailTrace_1246496 : CollatzResearch.WordTrace tailWord_1246496 prefixEnd_1246496 426701054604573541578317 := by
  unfold tailWord_1246496
  simp only [CollatzResearch.WordTrace]
  refine ⟨22731722046082675706651671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30308962728110234275535561 22731722046082675706651671)
  ·
    refine ⟨34097583069124013559977507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22731722046082675706651671 34097583069124013559977507)
    ·
      refine ⟨51146374603686020339966261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34097583069124013559977507 51146374603686020339966261)
      ·
        refine ⟨4794972619095564406871837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51146374603686020339966261 4794972619095564406871837)
        ·
          refine ⟨1798114732160836652576939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4794972619095564406871837 1798114732160836652576939)
          ·
            refine ⟨2697172098241254978865409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1798114732160836652576939 2697172098241254978865409)
            ·
              refine ⟨2022879073680941234149057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2697172098241254978865409 2022879073680941234149057)
              ·
                refine ⟨1517159305260705925611793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2022879073680941234149057 1517159305260705925611793)
                ·
                  refine ⟨1137869478945529444208845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1517159305260705925611793 1137869478945529444208845)
                  ·
                    refine ⟨426701054604573541578317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1137869478945529444208845 426701054604573541578317)
                    ·
                      rfl

theorem cell22_1246496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 2, 3].length) (baseStart_1246496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246496 prefixEnd_1246496 := by exact prefixLift 1246496
  have htrace : WordTrace (prefixWord ++ tailWord_1246496) baseStart_1246496 baseEnd_1246496 := by
    simpa [prefixWord, tailWord_1246496, baseEnd_1246496] using wordTrace_append hprefix tailTrace_1246496
  have hstable : (prefixWord ++ tailWord_1246496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246496).length < 2 ^ (prefixWord ++ tailWord_1246496).sum := by decide
  have hdescent : baseEnd_1246496 < baseStart_1246496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246498 : List Nat := [3, 3, 1, 1, 4, 2, 2, 2, 4]
def baseStart_1246498 : Nat := 118140960795 + 1246498 * 2 ^ 59
def prefixEnd_1246498 : Nat := 4983230072969 + 3 ^ 40 * 1246498 * 2
def baseEnd_1246498 : Nat := 142233913081815401009437

theorem tailTrace_1246498 : CollatzResearch.WordTrace tailWord_1246498 prefixEnd_1246498 142233913081815401009437 := by
  unfold tailWord_1246498
  simp only [CollatzResearch.WordTrace]
  refine ⟨11365879259539526438719037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30309011358772070503250765 11365879259539526438719037)
  ·
    refine ⟨4262204722327322414519639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11365879259539526438719037 4262204722327322414519639)
    ·
      refine ⟨6393307083490983621779459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4262204722327322414519639 6393307083490983621779459)
      ·
        refine ⟨9589960625236475432669189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6393307083490983621779459 9589960625236475432669189)
        ·
          refine ⟨1798117617231839143625473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9589960625236475432669189 1798117617231839143625473)
          ·
            refine ⟨1348588212923879357719105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1798117617231839143625473 1348588212923879357719105)
            ·
              refine ⟨1011441159692909518289329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1348588212923879357719105 1011441159692909518289329)
              ·
                refine ⟨758580869769682138716997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1011441159692909518289329 758580869769682138716997)
                ·
                  refine ⟨142233913081815401009437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 758580869769682138716997 142233913081815401009437)
                  ·
                    rfl

theorem cell22_1246498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_1246498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246498 prefixEnd_1246498 := by exact prefixLift 1246498
  have htrace : WordTrace (prefixWord ++ tailWord_1246498) baseStart_1246498 baseEnd_1246498 := by
    simpa [prefixWord, tailWord_1246498, baseEnd_1246498] using wordTrace_append hprefix tailTrace_1246498
  have hstable : (prefixWord ++ tailWord_1246498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246498).length < 2 ^ (prefixWord ++ tailWord_1246498).sum := by decide
  have hdescent : baseEnd_1246498 < baseStart_1246498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246509 : List Nat := [1, 5, 3, 1, 1, 1, 3, 7]
def baseStart_1246509 : Nat := 118140960795 + 1246509 * 2 ^ 59
def prefixEnd_1246509 : Nat := 4983230072969 + 3 ^ 40 * 1246509 * 2
def baseEnd_1246509 : Nat := 47411722752249537889253

theorem tailTrace_1246509 : CollatzResearch.WordTrace tailWord_1246509 prefixEnd_1246509 47411722752249537889253 := by
  unfold tailWord_1246509
  simp only [CollatzResearch.WordTrace]
  refine ⟨45463918241118254633526581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30309278827412169755684387 45463918241118254633526581)
  ·
    refine ⟨4262242335104836371893117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45463918241118254633526581 4262242335104836371893117)
    ·
      refine ⟨1598340875664313639459919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4262242335104836371893117 1598340875664313639459919)
      ·
        refine ⟨2397511313496470459189879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1598340875664313639459919 2397511313496470459189879)
        ·
          refine ⟨3596266970244705688784819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2397511313496470459189879 3596266970244705688784819)
          ·
            refine ⟨5394400455367058533177229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3596266970244705688784819 5394400455367058533177229)
            ·
              refine ⟨2022900170762646949941461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5394400455367058533177229 2022900170762646949941461)
              ·
                refine ⟨47411722752249537889253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2022900170762646949941461 47411722752249537889253)
                ·
                  rfl

theorem cell22_1246509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 7].length) (baseStart_1246509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246509 prefixEnd_1246509 := by exact prefixLift 1246509
  have htrace : WordTrace (prefixWord ++ tailWord_1246509) baseStart_1246509 baseEnd_1246509 := by
    simpa [prefixWord, tailWord_1246509, baseEnd_1246509] using wordTrace_append hprefix tailTrace_1246509
  have hstable : (prefixWord ++ tailWord_1246509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246509).length < 2 ^ (prefixWord ++ tailWord_1246509).sum := by decide
  have hdescent : baseEnd_1246509 < baseStart_1246509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246520 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 9]
def baseStart_1246520 : Nat := 118140960795 + 1246520 * 2 ^ 59
def prefixEnd_1246520 : Nat := 4983230072969 + 3 ^ 40 * 1246520 * 2
def baseEnd_1246520 : Nat := 142236423431681826326081

theorem tailTrace_1246520 : CollatzResearch.WordTrace tailWord_1246520 prefixEnd_1246520 142236423431681826326081 := by
  unfold tailWord_1246520
  simp only [CollatzResearch.WordTrace]
  refine ⟨22732159722039201756088507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30309546296052269008118009 22732159722039201756088507)
  ·
    refine ⟨34098239583058802634132761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22732159722039201756088507 34098239583058802634132761)
    ·
      refine ⟨25573679687294101975599571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34098239583058802634132761 25573679687294101975599571)
      ·
        refine ⟨38360519530941152963399357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25573679687294101975599571 38360519530941152963399357)
        ·
          refine ⟨14385194824102932361274759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38360519530941152963399357 14385194824102932361274759)
          ·
            refine ⟨21577792236154398541912139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14385194824102932361274759 21577792236154398541912139)
            ·
              refine ⟨32366688354231597812868209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21577792236154398541912139 32366688354231597812868209)
              ·
                refine ⟨24275016265673698359651157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32366688354231597812868209 24275016265673698359651157)
                ·
                  refine ⟨142236423431681826326081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 24275016265673698359651157 142236423431681826326081)
                  ·
                    rfl

theorem cell22_1246520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 9].length) (baseStart_1246520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246520 prefixEnd_1246520 := by exact prefixLift 1246520
  have htrace : WordTrace (prefixWord ++ tailWord_1246520) baseStart_1246520 baseEnd_1246520 := by
    simpa [prefixWord, tailWord_1246520, baseEnd_1246520] using wordTrace_append hprefix tailTrace_1246520
  have hstable : (prefixWord ++ tailWord_1246520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246520).length < 2 ^ (prefixWord ++ tailWord_1246520).sum := by decide
  have hdescent : baseEnd_1246520 < baseStart_1246520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246524 : List Nat := [2, 2, 2, 2, 1, 4, 1, 2, 3, 3]
def baseStart_1246524 : Nat := 118140960795 + 1246524 * 2 ^ 59
def prefixEnd_1246524 : Nat := 4983230072969 + 3 ^ 40 * 1246524 * 2
def baseEnd_1246524 : Nat := 426710639576790801878231

theorem tailTrace_1246524 : CollatzResearch.WordTrace tailWord_1246524 prefixEnd_1246524 426710639576790801878231 := by
  unfold tailWord_1246524
  simp only [CollatzResearch.WordTrace]
  refine ⟨22732232668031956097661313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30309643557375941463548417 22732232668031956097661313)
  ·
    refine ⟨17049174501023967073245985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22732232668031956097661313 17049174501023967073245985)
    ·
      refine ⟨12786880875767975304934489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17049174501023967073245985 12786880875767975304934489)
      ·
        refine ⟨9590160656825981478700867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12786880875767975304934489 9590160656825981478700867)
        ·
          refine ⟨14385240985238972218051301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9590160656825981478700867 14385240985238972218051301)
          ·
            refine ⟨2697232684732307290884619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14385240985238972218051301 2697232684732307290884619)
            ·
              refine ⟨4045849027098460936326929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2697232684732307290884619 4045849027098460936326929)
              ·
                refine ⟨3034386770323845702245197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4045849027098460936326929 3034386770323845702245197)
                ·
                  refine ⟨1137895038871442138341949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3034386770323845702245197 1137895038871442138341949)
                  ·
                    refine ⟨426710639576790801878231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1137895038871442138341949 426710639576790801878231)
                    ·
                      rfl

theorem cell22_1246524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_1246524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246524 prefixEnd_1246524 := by exact prefixLift 1246524
  have htrace : WordTrace (prefixWord ++ tailWord_1246524) baseStart_1246524 baseEnd_1246524 := by
    simpa [prefixWord, tailWord_1246524, baseEnd_1246524] using wordTrace_append hprefix tailTrace_1246524
  have hstable : (prefixWord ++ tailWord_1246524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246524).length < 2 ^ (prefixWord ++ tailWord_1246524).sum := by decide
  have hdescent : baseEnd_1246524 < baseStart_1246524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246597 : List Nat := [1, 3, 1, 1, 3, 1, 2, 4, 1, 5]
def baseStart_1246597 : Nat := 118140960795 + 1246597 * 2 ^ 59
def prefixEnd_1246597 : Nat := 4983230072969 + 3 ^ 40 * 1246597 * 2
def baseEnd_1246597 : Nat := 426735628968642944803007

theorem tailTrace_1246597 : CollatzResearch.WordTrace tailWord_1246597 prefixEnd_1246597 426735628968642944803007 := by
  unfold tailWord_1246597
  simp only [CollatzResearch.WordTrace]
  refine ⟨45467127864799445662730045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30311418576532963775153363 45467127864799445662730045)
  ·
    refine ⟨17050172949299792123523767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45467127864799445662730045 17050172949299792123523767)
    ·
      refine ⟨25575259423949688185285651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17050172949299792123523767 25575259423949688185285651)
      ·
        refine ⟨38362889135924532277928477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25575259423949688185285651 38362889135924532277928477)
        ·
          refine ⟨14386083425971699604223179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38362889135924532277928477 14386083425971699604223179)
          ·
            refine ⟨21579125138957549406334769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14386083425971699604223179 21579125138957549406334769)
            ·
              refine ⟨16184343854218162054751077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21579125138957549406334769 16184343854218162054751077)
              ·
                refine ⟨3034564472665905385265827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16184343854218162054751077 3034564472665905385265827)
                ·
                  refine ⟨4551846708998858077898741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3034564472665905385265827 4551846708998858077898741)
                  ·
                    refine ⟨426735628968642944803007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4551846708998858077898741 426735628968642944803007)
                    ·
                      rfl

theorem cell22_1246597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_1246597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246597 prefixEnd_1246597 := by exact prefixLift 1246597
  have htrace : WordTrace (prefixWord ++ tailWord_1246597) baseStart_1246597 baseEnd_1246597 := by
    simpa [prefixWord, tailWord_1246597, baseEnd_1246597] using wordTrace_append hprefix tailTrace_1246597
  have hstable : (prefixWord ++ tailWord_1246597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246597).length < 2 ^ (prefixWord ++ tailWord_1246597).sum := by decide
  have hdescent : baseEnd_1246597 < baseStart_1246597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246616 : List Nat := [2, 1, 2, 5, 2, 2, 1, 1, 6]
def baseStart_1246616 : Nat := 118140960795 + 1246616 * 2 ^ 59
def prefixEnd_1246616 : Nat := 4983230072969 + 3 ^ 40 * 1246616 * 2
def baseEnd_1246616 : Nat := 142247377685644409525983

theorem tailTrace_1246616 : CollatzResearch.WordTrace tailWord_1246616 prefixEnd_1246616 142247377685644409525983 := by
  unfold tailWord_1246616
  simp only [CollatzResearch.WordTrace]
  refine ⟨22733910425865305953835851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30311880567820407938447801 22733910425865305953835851)
  ·
    refine ⟨34100865638797958930753777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22733910425865305953835851 34100865638797958930753777)
    ·
      refine ⟨25575649229098469198065333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34100865638797958930753777 25575649229098469198065333)
      ·
        refine ⟨2397717115227981487318625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25575649229098469198065333 2397717115227981487318625)
        ·
          refine ⟨1798287836420986115488969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2397717115227981487318625 1798287836420986115488969)
          ·
            refine ⟨1348715877315739586616727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1798287836420986115488969 1348715877315739586616727)
            ·
              refine ⟨2023073815973609379925091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1348715877315739586616727 2023073815973609379925091)
              ·
                refine ⟨3034610723960414069887637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2023073815973609379925091 3034610723960414069887637)
                ·
                  refine ⟨142247377685644409525983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3034610723960414069887637 142247377685644409525983)
                  ·
                    rfl

theorem cell22_1246616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 6].length) (baseStart_1246616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246616 prefixEnd_1246616 := by exact prefixLift 1246616
  have htrace : WordTrace (prefixWord ++ tailWord_1246616) baseStart_1246616 baseEnd_1246616 := by
    simpa [prefixWord, tailWord_1246616, baseEnd_1246616] using wordTrace_append hprefix tailTrace_1246616
  have hstable : (prefixWord ++ tailWord_1246616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246616).length < 2 ^ (prefixWord ++ tailWord_1246616).sum := by decide
  have hdescent : baseEnd_1246616 < baseStart_1246616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246627 : List Nat := [1, 1, 1, 4, 1, 3, 4, 7]
def baseStart_1246627 : Nat := 118140960795 + 1246627 * 2 ^ 59
def prefixEnd_1246627 : Nat := 4983230072969 + 3 ^ 40 * 1246627 * 2
def baseEnd_1246627 : Nat := 47416210953525874061435

theorem tailTrace_1246627 : CollatzResearch.WordTrace tailWord_1246627 prefixEnd_1246627 47416210953525874061435 := by
  unfold tailWord_1246627
  simp only [CollatzResearch.WordTrace]
  refine ⟨45468222054690760786322135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30312148036460507190881423 45468222054690760786322135)
  ·
    refine ⟨68202333082036141179483203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45468222054690760786322135 68202333082036141179483203)
    ·
      refine ⟨102303499623054211769224805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68202333082036141179483203 102303499623054211769224805)
      ·
        refine ⟨19181906179322664706729651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102303499623054211769224805 19181906179322664706729651)
        ·
          refine ⟨28772859268983997060094477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19181906179322664706729651 28772859268983997060094477)
          ·
            refine ⟨10789822225868998897535429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28772859268983997060094477 10789822225868998897535429)
            ·
              refine ⟨2023091667350437293287893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10789822225868998897535429 2023091667350437293287893)
              ·
                refine ⟨47416210953525874061435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2023091667350437293287893 47416210953525874061435)
                ·
                  rfl

theorem cell22_1246627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 7].length) (baseStart_1246627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246627 prefixEnd_1246627 := by exact prefixLift 1246627
  have htrace : WordTrace (prefixWord ++ tailWord_1246627) baseStart_1246627 baseEnd_1246627 := by
    simpa [prefixWord, tailWord_1246627, baseEnd_1246627] using wordTrace_append hprefix tailTrace_1246627
  have hstable : (prefixWord ++ tailWord_1246627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246627).length < 2 ^ (prefixWord ++ tailWord_1246627).sum := by decide
  have hdescent : baseEnd_1246627 < baseStart_1246627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246631 : List Nat := [1, 1, 6, 1, 1, 1, 3, 3, 2, 3]
def baseStart_1246631 : Nat := 118140960795 + 1246631 * 2 ^ 59
def prefixEnd_1246631 : Nat := 4983230072969 + 3 ^ 40 * 1246631 * 2
def baseEnd_1246631 : Nat := 426747267863478189452903

theorem tailTrace_1246631 : CollatzResearch.WordTrace tailWord_1246631 prefixEnd_1246631 426747267863478189452903 := by
  unfold tailWord_1246631
  simp only [CollatzResearch.WordTrace]
  refine ⟨45468367946676269469467747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30312245297784179646311831 45468367946676269469467747)
  ·
    refine ⟨68202551920014404204201621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45468367946676269469467747 68202551920014404204201621)
    ·
      refine ⟨3196994621250675197071951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 68202551920014404204201621 3196994621250675197071951)
      ·
        refine ⟨4795491931876012795607927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3196994621250675197071951 4795491931876012795607927)
        ·
          refine ⟨7193237897814019193411891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4795491931876012795607927 7193237897814019193411891)
          ·
            refine ⟨10789856846721028790117837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7193237897814019193411891 10789856846721028790117837)
            ·
              refine ⟨4046196317520385796294189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10789856846721028790117837 4046196317520385796294189)
              ·
                refine ⟨1517323619070144673610321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4046196317520385796294189 1517323619070144673610321)
                ·
                  refine ⟨1137992714302608505207741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1517323619070144673610321 1137992714302608505207741)
                  ·
                    refine ⟨426747267863478189452903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1137992714302608505207741 426747267863478189452903)
                    ·
                      rfl

theorem cell22_1246631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_1246631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246631 prefixEnd_1246631 := by exact prefixLift 1246631
  have htrace : WordTrace (prefixWord ++ tailWord_1246631) baseStart_1246631 baseEnd_1246631 := by
    simpa [prefixWord, tailWord_1246631, baseEnd_1246631] using wordTrace_append hprefix tailTrace_1246631
  have hstable : (prefixWord ++ tailWord_1246631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246631).length < 2 ^ (prefixWord ++ tailWord_1246631).sum := by decide
  have hdescent : baseEnd_1246631 < baseStart_1246631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246689 : List Nat := [1, 2, 3, 1, 2, 3, 2, 3, 5]
def baseStart_1246689 : Nat := 118140960795 + 1246689 * 2 ^ 59
def prefixEnd_1246689 : Nat := 4983230072969 + 3 ^ 40 * 1246689 * 2
def baseEnd_1246689 : Nat := 142255707482928457167575

theorem tailTrace_1246689 : CollatzResearch.WordTrace tailWord_1246689 prefixEnd_1246689 142255707482928457167575 := by
  unfold tailWord_1246689
  simp only [CollatzResearch.WordTrace]
  refine ⟨45470483380466145375079121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30313655586977430250052747 45470483380466145375079121)
  ·
    refine ⟨34102862535349609031309341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45470483380466145375079121 34102862535349609031309341)
    ·
      refine ⟨12788573450756103386741003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34102862535349609031309341 12788573450756103386741003)
      ·
        refine ⟨19182860176134155080111505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12788573450756103386741003 19182860176134155080111505)
        ·
          refine ⟨14387145132100616310083629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19182860176134155080111505 14387145132100616310083629)
          ·
            refine ⟨5395179424537731116281361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14387145132100616310083629 5395179424537731116281361)
            ·
              refine ⟨4046384568403298337211021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5395179424537731116281361 4046384568403298337211021)
              ·
                refine ⟨1517394213151236876454133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4046384568403298337211021 1517394213151236876454133)
                ·
                  refine ⟨142255707482928457167575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1517394213151236876454133 142255707482928457167575)
                  ·
                    rfl

theorem cell22_1246689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3, 5].length) (baseStart_1246689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246689 prefixEnd_1246689 := by exact prefixLift 1246689
  have htrace : WordTrace (prefixWord ++ tailWord_1246689) baseStart_1246689 baseEnd_1246689 := by
    simpa [prefixWord, tailWord_1246689, baseEnd_1246689] using wordTrace_append hprefix tailTrace_1246689
  have hstable : (prefixWord ++ tailWord_1246689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246689).length < 2 ^ (prefixWord ++ tailWord_1246689).sum := by decide
  have hdescent : baseEnd_1246689 < baseStart_1246689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246710 : List Nat := [5, 1, 1, 1, 2, 3, 2, 3, 1, 3]
def baseStart_1246710 : Nat := 118140960795 + 1246710 * 2 ^ 59
def prefixEnd_1246710 : Nat := 4983230072969 + 3 ^ 40 * 1246710 * 2
def baseEnd_1246710 : Nat := 426774311177948316727661

theorem tailTrace_1246710 : CollatzResearch.WordTrace tailWord_1246710 prefixEnd_1246710 426774311177948316727661 := by
  unfold tailWord_1246710
  simp only [CollatzResearch.WordTrace]
  refine ⟨2841953082086879122599599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30314166208926710641062389 2841953082086879122599599)
  ·
    refine ⟨4262929623130318683899399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2841953082086879122599599 4262929623130318683899399)
    ·
      refine ⟨6394394434695478025849099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4262929623130318683899399 6394394434695478025849099)
      ·
        refine ⟨9591591652043217038773649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6394394434695478025849099 9591591652043217038773649)
        ·
          refine ⟨7193693739032412779080237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9591591652043217038773649 7193693739032412779080237)
          ·
            refine ⟨2697635152137154792155089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7193693739032412779080237 2697635152137154792155089)
            ·
              refine ⟨2023226364102866094116317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2697635152137154792155089 2023226364102866094116317)
              ·
                refine ⟨758709886538574785293619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2023226364102866094116317 758709886538574785293619)
                ·
                  refine ⟨1138064829807862177940429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 758709886538574785293619 1138064829807862177940429)
                  ·
                    refine ⟨426774311177948316727661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1138064829807862177940429 426774311177948316727661)
                    ·
                      rfl

theorem cell22_1246710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_1246710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246710 prefixEnd_1246710 := by exact prefixLift 1246710
  have htrace : WordTrace (prefixWord ++ tailWord_1246710) baseStart_1246710 baseEnd_1246710 := by
    simpa [prefixWord, tailWord_1246710, baseEnd_1246710] using wordTrace_append hprefix tailTrace_1246710
  have hstable : (prefixWord ++ tailWord_1246710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246710).length < 2 ^ (prefixWord ++ tailWord_1246710).sum := by decide
  have hdescent : baseEnd_1246710 < baseStart_1246710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246740 : List Nat := [2, 4, 3, 1, 2, 1, 3, 1, 5]
def baseStart_1246740 : Nat := 118140960795 + 1246740 * 2 ^ 59
def prefixEnd_1246740 : Nat := 4983230072969 + 3 ^ 40 * 1246740 * 2
def baseEnd_1246740 : Nat := 142261526930346079492523

theorem tailTrace_1246740 : CollatzResearch.WordTrace tailWord_1246740 prefixEnd_1246740 142261526930346079492523 := by
  unfold tailWord_1246740
  simp only [CollatzResearch.WordTrace]
  refine ⟨22736171751640690542592837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30314895668854254056790449 22736171751640690542592837)
  ·
    refine ⟨4263032203432629476736157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22736171751640690542592837 4263032203432629476736157)
    ·
      refine ⟨1598637076287236053776059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4263032203432629476736157 1598637076287236053776059)
      ·
        refine ⟨2397955614430854080664089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1598637076287236053776059 2397955614430854080664089)
        ·
          refine ⟨1798466710823140560498067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2397955614430854080664089 1798466710823140560498067)
          ·
            refine ⟨2697700066234710840747101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1798466710823140560498067 2697700066234710840747101)
            ·
              refine ⟨1011637524838016565280163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2697700066234710840747101 1011637524838016565280163)
              ·
                refine ⟨1517456287257024847920245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1011637524838016565280163 1517456287257024847920245)
                ·
                  refine ⟨142261526930346079492523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1517456287257024847920245 142261526930346079492523)
                  ·
                    rfl

theorem cell22_1246740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_1246740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246740 prefixEnd_1246740 := by exact prefixLift 1246740
  have htrace : WordTrace (prefixWord ++ tailWord_1246740) baseStart_1246740 baseEnd_1246740 := by
    simpa [prefixWord, tailWord_1246740, baseEnd_1246740] using wordTrace_append hprefix tailTrace_1246740
  have hstable : (prefixWord ++ tailWord_1246740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246740).length < 2 ^ (prefixWord ++ tailWord_1246740).sum := by decide
  have hdescent : baseEnd_1246740 < baseStart_1246740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246828 : List Nat := [2, 2, 1, 1, 3, 1, 1, 7, 1, 3]
def baseStart_1246828 : Nat := 118140960795 + 1246828 * 2 ^ 59
def prefixEnd_1246828 : Nat := 4983230072969 + 3 ^ 40 * 1246828 * 2
def baseEnd_1246828 : Nat := 426814704989435342277299

theorem tailTrace_1246828 : CollatzResearch.WordTrace tailWord_1246828 prefixEnd_1246828 426814704989435342277299 := by
  unfold tailWord_1246828
  simp only [CollatzResearch.WordTrace]
  refine ⟨22737776563481286057194569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30317035417975048076259425 22737776563481286057194569)
  ·
    refine ⟨17053332422610964542895927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22737776563481286057194569 17053332422610964542895927)
    ·
      refine ⟨25579998633916446814343891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17053332422610964542895927 25579998633916446814343891)
      ·
        refine ⟨38369997950874670221515837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25579998633916446814343891 38369997950874670221515837)
        ·
          refine ⟨14388749231578001333068439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38369997950874670221515837 14388749231578001333068439)
          ·
            refine ⟨21583123847367001999602659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14388749231578001333068439 21583123847367001999602659)
            ·
              refine ⟨32374685771050502999403989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21583123847367001999602659 32374685771050502999403989)
              ·
                refine ⟨758781697758996164048531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 32374685771050502999403989 758781697758996164048531)
                ·
                  refine ⟨1138172546638494246072797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 758781697758996164048531 1138172546638494246072797)
                  ·
                    refine ⟨426814704989435342277299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1138172546638494246072797 426814704989435342277299)
                    ·
                      rfl

theorem cell22_1246828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 7, 1, 3].length) (baseStart_1246828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246828 prefixEnd_1246828 := by exact prefixLift 1246828
  have htrace : WordTrace (prefixWord ++ tailWord_1246828) baseStart_1246828 baseEnd_1246828 := by
    simpa [prefixWord, tailWord_1246828, baseEnd_1246828] using wordTrace_append hprefix tailTrace_1246828
  have hstable : (prefixWord ++ tailWord_1246828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246828).length < 2 ^ (prefixWord ++ tailWord_1246828).sum := by decide
  have hdescent : baseEnd_1246828 < baseStart_1246828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246839 : List Nat := [1, 1, 3, 1, 1, 3, 1, 4, 2, 5]
def baseStart_1246839 : Nat := 118140960795 + 1246839 * 2 ^ 59
def prefixEnd_1246839 : Nat := 4983230072969 + 3 ^ 40 * 1246839 * 2
def baseEnd_1246839 : Nat := 426818470514234980252265

theorem tailTrace_1246839 : CollatzResearch.WordTrace tailWord_1246839 prefixEnd_1246839 426818470514234980252265 := by
  unfold tailWord_1246839
  simp only [CollatzResearch.WordTrace]
  refine ⟨45475954329922720993039571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30317302886615147328693047 45475954329922720993039571)
  ·
    refine ⟨68213931494884081489559357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45475954329922720993039571 68213931494884081489559357)
    ·
      refine ⟨25580224310581530558584759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68213931494884081489559357 25580224310581530558584759)
      ·
        refine ⟨38370336465872295837877139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25580224310581530558584759 38370336465872295837877139)
        ·
          refine ⟨57555504698808443756815709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38370336465872295837877139 57555504698808443756815709)
          ·
            refine ⟨21583314262053166408805891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57555504698808443756815709 21583314262053166408805891)
            ·
              refine ⟨32374971393079749613208837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21583314262053166408805891 32374971393079749613208837)
              ·
                refine ⟨6070307136202453052476657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32374971393079749613208837 6070307136202453052476657)
                ·
                  refine ⟨4552730352151839789357493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6070307136202453052476657 4552730352151839789357493)
                  ·
                    refine ⟨426818470514234980252265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4552730352151839789357493 426818470514234980252265)
                    ·
                      rfl

theorem cell22_1246839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_1246839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246839 prefixEnd_1246839 := by exact prefixLift 1246839
  have htrace : WordTrace (prefixWord ++ tailWord_1246839) baseStart_1246839 baseEnd_1246839 := by
    simpa [prefixWord, tailWord_1246839, baseEnd_1246839] using wordTrace_append hprefix tailTrace_1246839
  have hstable : (prefixWord ++ tailWord_1246839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246839).length < 2 ^ (prefixWord ++ tailWord_1246839).sum := by decide
  have hdescent : baseEnd_1246839 < baseStart_1246839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246841 : List Nat := [1, 2, 1, 3, 3, 1, 4, 2, 5]
def baseStart_1246841 : Nat := 118140960795 + 1246841 * 2 ^ 59
def prefixEnd_1246841 : Nat := 4983230072969 + 3 ^ 40 * 1246841 * 2
def baseEnd_1246841 : Nat := 142273051718369213900753

theorem tailTrace_1246841 : CollatzResearch.WordTrace tailWord_1246841 prefixEnd_1246841 142273051718369213900753 := by
  unfold tailWord_1246841
  simp only [CollatzResearch.WordTrace]
  refine ⟨45476027275915475334612377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30317351517276983556408251 45476027275915475334612377)
  ·
    refine ⟨34107020456936606500959283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45476027275915475334612377 34107020456936606500959283)
    ·
      refine ⟨51160530685404909751438925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34107020456936606500959283 51160530685404909751438925)
      ·
        refine ⟨19185199007026841156789597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51160530685404909751438925 19185199007026841156789597)
        ·
          refine ⟨7194449627635065433796099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19185199007026841156789597 7194449627635065433796099)
          ·
            refine ⟨10791674441452598150694149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7194449627635065433796099 10791674441452598150694149)
            ·
              refine ⟨2023438957772362153255153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10791674441452598150694149 2023438957772362153255153)
              ·
                refine ⟨1517579218329271614941365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2023438957772362153255153 1517579218329271614941365)
                ·
                  refine ⟨142273051718369213900753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1517579218329271614941365 142273051718369213900753)
                  ·
                    rfl

theorem cell22_1246841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 5].length) (baseStart_1246841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246841 prefixEnd_1246841 := by exact prefixLift 1246841
  have htrace : WordTrace (prefixWord ++ tailWord_1246841) baseStart_1246841 baseEnd_1246841 := by
    simpa [prefixWord, tailWord_1246841, baseEnd_1246841] using wordTrace_append hprefix tailTrace_1246841
  have hstable : (prefixWord ++ tailWord_1246841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246841).length < 2 ^ (prefixWord ++ tailWord_1246841).sum := by decide
  have hdescent : baseEnd_1246841 < baseStart_1246841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246845 : List Nat := [1, 4, 1, 1, 4, 2, 1, 4, 1, 3]
def baseStart_1246845 : Nat := 118140960795 + 1246845 * 2 ^ 59
def prefixEnd_1246845 : Nat := 4983230072969 + 3 ^ 40 * 1246845 * 2
def baseEnd_1246845 : Nat := 426820524436852964602247

theorem tailTrace_1246845 : CollatzResearch.WordTrace tailWord_1246845 prefixEnd_1246845 426820524436852964602247 := by
  unfold tailWord_1246845
  simp only [CollatzResearch.WordTrace]
  refine ⟨45476173167900984017757989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30317448778600656011838659 45476173167900984017757989)
  ·
    refine ⟨8526782468981434503329623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45476173167900984017757989 8526782468981434503329623)
    ·
      refine ⟨12790173703472151754994435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8526782468981434503329623 12790173703472151754994435)
      ·
        refine ⟨19185260555208227632491653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12790173703472151754994435 19185260555208227632491653)
        ·
          refine ⟨3597236354101542681092185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19185260555208227632491653 3597236354101542681092185)
          ·
            refine ⟨2697927265576157010819139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3597236354101542681092185 2697927265576157010819139)
            ·
              refine ⟨4046890898364235516228709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2697927265576157010819139 4046890898364235516228709)
              ·
                refine ⟨758792043443294159292883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4046890898364235516228709 758792043443294159292883)
                ·
                  refine ⟨1138188065164941238939325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 758792043443294159292883 1138188065164941238939325)
                  ·
                    refine ⟨426820524436852964602247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1138188065164941238939325 426820524436852964602247)
                    ·
                      rfl

theorem cell22_1246845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 4, 1, 3].length) (baseStart_1246845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246845 prefixEnd_1246845 := by exact prefixLift 1246845
  have htrace : WordTrace (prefixWord ++ tailWord_1246845) baseStart_1246845 baseEnd_1246845 := by
    simpa [prefixWord, tailWord_1246845, baseEnd_1246845] using wordTrace_append hprefix tailTrace_1246845
  have hstable : (prefixWord ++ tailWord_1246845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246845).length < 2 ^ (prefixWord ++ tailWord_1246845).sum := by decide
  have hdescent : baseEnd_1246845 < baseStart_1246845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246871 : List Nat := [1, 1, 3, 3, 2, 2, 2, 1, 3, 4]
def baseStart_1246871 : Nat := 118140960795 + 1246871 * 2 ^ 59
def prefixEnd_1246871 : Nat := 4983230072969 + 3 ^ 40 * 1246871 * 2
def baseEnd_1246871 : Nat := 426829424768197563452167

theorem tailTrace_1246871 : CollatzResearch.WordTrace tailWord_1246871 prefixEnd_1246871 426829424768197563452167 := by
  unfold tailWord_1246871
  simp only [CollatzResearch.WordTrace]
  refine ⟨45477121465806790458204467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30318080977204526972136311 45477121465806790458204467)
  ·
    refine ⟨68215682198710185687306701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45477121465806790458204467 68215682198710185687306701)
    ·
      refine ⟨25580880824516319632740013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68215682198710185687306701 25580880824516319632740013)
      ·
        refine ⟨9592830309193619862277505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25580880824516319632740013 9592830309193619862277505)
        ·
          refine ⟨7194622731895214896708129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9592830309193619862277505 7194622731895214896708129)
          ·
            refine ⟨5395967048921411172531097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7194622731895214896708129 5395967048921411172531097)
            ·
              refine ⟨4046975286691058379398323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5395967048921411172531097 4046975286691058379398323)
              ·
                refine ⟨6070462930036587569097485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4046975286691058379398323 6070462930036587569097485)
                ·
                  refine ⟨2276423598763720338411557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6070462930036587569097485 2276423598763720338411557)
                  ·
                    refine ⟨426829424768197563452167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2276423598763720338411557 426829424768197563452167)
                    ·
                      rfl

theorem cell22_1246871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_1246871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246871 prefixEnd_1246871 := by exact prefixLift 1246871
  have htrace : WordTrace (prefixWord ++ tailWord_1246871) baseStart_1246871 baseEnd_1246871 := by
    simpa [prefixWord, tailWord_1246871, baseEnd_1246871] using wordTrace_append hprefix tailTrace_1246871
  have hstable : (prefixWord ++ tailWord_1246871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246871).length < 2 ^ (prefixWord ++ tailWord_1246871).sum := by decide
  have hdescent : baseEnd_1246871 < baseStart_1246871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246903 : List Nat := [1, 1, 3, 1, 5, 1, 2, 4, 4]
def baseStart_1246903 : Nat := 118140960795 + 1246903 * 2 ^ 59
def prefixEnd_1246903 : Nat := 4983230072969 + 3 ^ 40 * 1246903 * 2
def baseEnd_1246903 : Nat := 142280126340720048884023

theorem tailTrace_1246903 : CollatzResearch.WordTrace tailWord_1246903 prefixEnd_1246903 142280126340720048884023 := by
  unfold tailWord_1246903
  simp only [CollatzResearch.WordTrace]
  refine ⟨45478288601690859923369363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30318859067793906615579575 45478288601690859923369363)
  ·
    refine ⟨68217432902536289885054045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45478288601690859923369363 68217432902536289885054045)
    ·
      refine ⟨25581537338451108706895267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68217432902536289885054045 25581537338451108706895267)
      ·
        refine ⟨38372306007676663060342901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25581537338451108706895267 38372306007676663060342901)
        ·
          refine ⟨3597403688219687161907147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38372306007676663060342901 3597403688219687161907147)
          ·
            refine ⟨5396105532329530742860721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3597403688219687161907147 5396105532329530742860721)
            ·
              refine ⟨4047079149247148057145541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5396105532329530742860721 4047079149247148057145541)
              ·
                refine ⟨758827340483840260714789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4047079149247148057145541 758827340483840260714789)
                ·
                  refine ⟨142280126340720048884023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 758827340483840260714789 142280126340720048884023)
                  ·
                    rfl

theorem cell22_1246903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 4, 4].length) (baseStart_1246903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246903 prefixEnd_1246903 := by exact prefixLift 1246903
  have htrace : WordTrace (prefixWord ++ tailWord_1246903) baseStart_1246903 baseEnd_1246903 := by
    simpa [prefixWord, tailWord_1246903, baseEnd_1246903] using wordTrace_append hprefix tailTrace_1246903
  have hstable : (prefixWord ++ tailWord_1246903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246903).length < 2 ^ (prefixWord ++ tailWord_1246903).sum := by decide
  have hdescent : baseEnd_1246903 < baseStart_1246903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246916 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 3, 6]
def baseStart_1246916 : Nat := 118140960795 + 1246916 * 2 ^ 59
def prefixEnd_1246916 : Nat := 4983230072969 + 3 ^ 40 * 1246916 * 2
def baseEnd_1246916 : Nat := 426844829187832446077029

theorem tailTrace_1246916 : CollatzResearch.WordTrace tailWord_1246916 prefixEnd_1246916 426844829187832446077029 := by
  unfold tailWord_1246916
  simp only [CollatzResearch.WordTrace]
  refine ⟨22739381375321881571796301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30319175167095842095728401 22739381375321881571796301)
  ·
    refine ⟨8527268015745705589423613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22739381375321881571796301 8527268015745705589423613)
    ·
      refine ⟨3197725505904639596033855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8527268015745705589423613 3197725505904639596033855)
      ·
        refine ⟨4796588258856959394050783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3197725505904639596033855 4796588258856959394050783)
        ·
          refine ⟨7194882388285439091076175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4796588258856959394050783 7194882388285439091076175)
          ·
            refine ⟨10792323582428158636614263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7194882388285439091076175 10792323582428158636614263)
            ·
              refine ⟨16188485373642237954921395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10792323582428158636614263 16188485373642237954921395)
              ·
                refine ⟨24282728060463356932382093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16188485373642237954921395 24282728060463356932382093)
                ·
                  refine ⟨9106023022673758849643285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24282728060463356932382093 9106023022673758849643285)
                  ·
                    refine ⟨426844829187832446077029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9106023022673758849643285 426844829187832446077029)
                    ·
                      rfl

theorem cell22_1246916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_1246916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246916 prefixEnd_1246916 := by exact prefixLift 1246916
  have htrace : WordTrace (prefixWord ++ tailWord_1246916) baseStart_1246916 baseEnd_1246916 := by
    simpa [prefixWord, tailWord_1246916, baseEnd_1246916] using wordTrace_append hprefix tailTrace_1246916
  have hstable : (prefixWord ++ tailWord_1246916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246916).length < 2 ^ (prefixWord ++ tailWord_1246916).sum := by decide
  have hdescent : baseEnd_1246916 < baseStart_1246916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246963 : List Nat := [1, 1, 1, 2, 2, 3, 5, 1, 3, 3]
def baseStart_1246963 : Nat := 118140960795 + 1246963 * 2 ^ 59
def prefixEnd_1246963 : Nat := 4983230072969 + 3 ^ 40 * 1246963 * 2
def baseEnd_1246963 : Nat := 426860918248339990151885

theorem tailTrace_1246963 : CollatzResearch.WordTrace tailWord_1246963 prefixEnd_1246963 426860918248339990151885 := by
  unfold tailWord_1246963
  simp only [CollatzResearch.WordTrace]
  refine ⟨45480476981473490170553543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30320317987648993447035695 45480476981473490170553543)
  ·
    refine ⟨68220715472210235255830315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45480476981473490170553543 68220715472210235255830315)
    ·
      refine ⟨102331073208315352883745473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68220715472210235255830315 102331073208315352883745473)
      ·
        refine ⟨76748304906236514662809105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102331073208315352883745473 76748304906236514662809105)
        ·
          refine ⟨57561228679677385997106829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76748304906236514662809105 57561228679677385997106829)
          ·
            refine ⟨21585460754879019748915061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57561228679677385997106829 21585460754879019748915061)
            ·
              refine ⟨2023636945769908101460787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21585460754879019748915061 2023636945769908101460787)
              ·
                refine ⟨3035455418654862152191181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2023636945769908101460787 3035455418654862152191181)
                ·
                  refine ⟨1138295781995573307071693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3035455418654862152191181 1138295781995573307071693)
                  ·
                    refine ⟨426860918248339990151885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1138295781995573307071693 426860918248339990151885)
                    ·
                      rfl

theorem cell22_1246963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 3, 3].length) (baseStart_1246963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246963 prefixEnd_1246963 := by exact prefixLift 1246963
  have htrace : WordTrace (prefixWord ++ tailWord_1246963) baseStart_1246963 baseEnd_1246963 := by
    simpa [prefixWord, tailWord_1246963, baseEnd_1246963] using wordTrace_append hprefix tailTrace_1246963
  have hstable : (prefixWord ++ tailWord_1246963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246963).length < 2 ^ (prefixWord ++ tailWord_1246963).sum := by decide
  have hdescent : baseEnd_1246963 < baseStart_1246963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246976 : List Nat := [2, 1, 1, 2, 1, 1, 2, 7, 5]
def baseStart_1246976 : Nat := 118140960795 + 1246976 * 2 ^ 59
def prefixEnd_1246976 : Nat := 4983230072969 + 3 ^ 40 * 1246976 * 2
def baseEnd_1246976 : Nat := 142288456138004096525615

theorem tailTrace_1246976 : CollatzResearch.WordTrace tailWord_1246976 prefixEnd_1246976 142288456138004096525615 := by
  unfold tailWord_1246976
  simp only [CollatzResearch.WordTrace]
  refine ⟨22740475565213196695388391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30320634086950928927184521 22740475565213196695388391)
  ·
    refine ⟨34110713347819795043082587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22740475565213196695388391 34110713347819795043082587)
    ·
      refine ⟨51166070021729692564623881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34110713347819795043082587 51166070021729692564623881)
      ·
        refine ⟨38374552516297269423467911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51166070021729692564623881 38374552516297269423467911)
        ·
          refine ⟨57561828774445904135201867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38374552516297269423467911 57561828774445904135201867)
          ·
            refine ⟨86342743161668856202802801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57561828774445904135201867 86342743161668856202802801)
            ·
              refine ⟨64757057371251642152102101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86342743161668856202802801 64757057371251642152102101)
              ·
                refine ⟨1517743532138710362939893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 64757057371251642152102101 1517743532138710362939893)
                ·
                  refine ⟨142288456138004096525615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1517743532138710362939893 142288456138004096525615)
                  ·
                    rfl

theorem cell22_1246976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 5].length) (baseStart_1246976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1246976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1246976 prefixEnd_1246976 := by exact prefixLift 1246976
  have htrace : WordTrace (prefixWord ++ tailWord_1246976) baseStart_1246976 baseEnd_1246976 := by
    simpa [prefixWord, tailWord_1246976, baseEnd_1246976] using wordTrace_append hprefix tailTrace_1246976
  have hstable : (prefixWord ++ tailWord_1246976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246976).length < 2 ^ (prefixWord ++ tailWord_1246976).sum := by decide
  have hdescent : baseEnd_1246976 < baseStart_1246976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247038 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 8]
def baseStart_1247038 : Nat := 118140960795 + 1247038 * 2 ^ 59
def prefixEnd_1247038 : Nat := 4983230072969 + 3 ^ 40 * 1247038 * 2
def baseEnd_1247038 : Nat := 142295530760354931508885

theorem tailTrace_1247038 : CollatzResearch.WordTrace tailWord_1247038 prefixEnd_1247038 142295530760354931508885 := by
  unfold tailWord_1247038
  simp only [CollatzResearch.WordTrace]
  refine ⟨5685401557025222247441721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30322141637467851986355845 5685401557025222247441721)
  ·
    refine ⟨4264051167768916685581291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5685401557025222247441721 4264051167768916685581291)
    ·
      refine ⟨6396076751653375028371937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4264051167768916685581291 6396076751653375028371937)
      ·
        refine ⟨4797057563740031271278953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6396076751653375028371937 4797057563740031271278953)
        ·
          refine ⟨3597793172805023453459215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4797057563740031271278953 3597793172805023453459215)
          ·
            refine ⟨5396689759207535180188823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3597793172805023453459215 5396689759207535180188823)
            ·
              refine ⟨8095034638811302770283235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5396689759207535180188823 8095034638811302770283235)
              ·
                refine ⟨12142551958216954155424853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8095034638811302770283235 12142551958216954155424853)
                ·
                  refine ⟨142295530760354931508885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12142551958216954155424853 142295530760354931508885)
                  ·
                    rfl

theorem cell22_1247038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_1247038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1247038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1247038 prefixEnd_1247038 := by exact prefixLift 1247038
  have htrace : WordTrace (prefixWord ++ tailWord_1247038) baseStart_1247038 baseEnd_1247038 := by
    simpa [prefixWord, tailWord_1247038, baseEnd_1247038] using wordTrace_append hprefix tailTrace_1247038
  have hstable : (prefixWord ++ tailWord_1247038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247038).length < 2 ^ (prefixWord ++ tailWord_1247038).sum := by decide
  have hdescent : baseEnd_1247038 < baseStart_1247038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247057 : List Nat := [1, 2, 2, 1, 5, 3, 2, 1, 1, 4]
def baseStart_1247057 : Nat := 118140960795 + 1247057 * 2 ^ 59
def prefixEnd_1247057 : Nat := 4983230072969 + 3 ^ 40 * 1247057 * 2
def baseEnd_1247057 : Nat := 426893096369355078301597

theorem tailTrace_1247057 : CollatzResearch.WordTrace tailWord_1247057 prefixEnd_1247057 426893096369355078301597 := by
  unfold tailWord_1247057
  simp only [CollatzResearch.WordTrace]
  refine ⟨45483905443132944224475425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30322603628755296149650283 45483905443132944224475425)
  ·
    refine ⟨34112929082349708168356569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45483905443132944224475425 34112929082349708168356569)
    ·
      refine ⟨25584696811762281126267427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34112929082349708168356569 25584696811762281126267427)
      ·
        refine ⟨38377045217643421689401141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25584696811762281126267427 38377045217643421689401141)
        ·
          refine ⟨3597847989154070783381357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38377045217643421689401141 3597847989154070783381357)
          ·
            refine ⟨1349192995932776543768009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3597847989154070783381357 1349192995932776543768009)
            ·
              refine ⟨1011894746949582407826007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1349192995932776543768009 1011894746949582407826007)
              ·
                refine ⟨1517842120424373611739011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1011894746949582407826007 1517842120424373611739011)
                ·
                  refine ⟨2276763180636560417608517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1517842120424373611739011 2276763180636560417608517)
                  ·
                    refine ⟨426893096369355078301597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2276763180636560417608517 426893096369355078301597)
                    ·
                      rfl

theorem cell22_1247057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 1, 4].length) (baseStart_1247057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1247057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1247057 prefixEnd_1247057 := by exact prefixLift 1247057
  have htrace : WordTrace (prefixWord ++ tailWord_1247057) baseStart_1247057 baseEnd_1247057 := by
    simpa [prefixWord, tailWord_1247057, baseEnd_1247057] using wordTrace_append hprefix tailTrace_1247057
  have hstable : (prefixWord ++ tailWord_1247057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247057).length < 2 ^ (prefixWord ++ tailWord_1247057).sum := by decide
  have hdescent : baseEnd_1247057 < baseStart_1247057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247066 : List Nat := [3, 1, 1, 2, 1, 3, 11]
def baseStart_1247066 : Nat := 118140960795 + 1247066 * 2 ^ 59
def prefixEnd_1247066 : Nat := 4983230072969 + 3 ^ 40 * 1247066 * 2
def baseEnd_1247066 : Nat := 15810969527899335363947

theorem tailTrace_1247066 : CollatzResearch.WordTrace tailWord_1247066 prefixEnd_1247066 15810969527899335363947 := by
  unfold tailWord_1247066
  simp only [CollatzResearch.WordTrace]
  refine ⟨11371058425025084690388263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30322822466733559174368701 11371058425025084690388263)
  ·
    refine ⟨17056587637537627035582395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11371058425025084690388263 17056587637537627035582395)
    ·
      refine ⟨25584881456306440553373593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17056587637537627035582395 25584881456306440553373593)
      ·
        refine ⟨19188661092229830415030195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25584881456306440553373593 19188661092229830415030195)
        ·
          refine ⟨28782991638344745622545293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19188661092229830415030195 28782991638344745622545293)
          ·
            refine ⟨10793621864379279608454485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28782991638344745622545293 10793621864379279608454485)
            ·
              refine ⟨15810969527899335363947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 10793621864379279608454485 15810969527899335363947)
              ·
                rfl

theorem cell22_1247066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 11].length) (baseStart_1247066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1247066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1247066 prefixEnd_1247066 := by exact prefixLift 1247066
  have htrace : WordTrace (prefixWord ++ tailWord_1247066) baseStart_1247066 baseEnd_1247066 := by
    simpa [prefixWord, tailWord_1247066, baseEnd_1247066] using wordTrace_append hprefix tailTrace_1247066
  have hstable : (prefixWord ++ tailWord_1247066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247066).length < 2 ^ (prefixWord ++ tailWord_1247066).sum := by decide
  have hdescent : baseEnd_1247066 < baseStart_1247066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247096 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 3, 8]
def baseStart_1247096 : Nat := 118140960795 + 1247096 * 2 ^ 59
def prefixEnd_1247096 : Nat := 4983230072969 + 3 ^ 40 * 1247096 * 2
def baseEnd_1247096 : Nat := 426906446866371976576477

theorem tailTrace_1247096 : CollatzResearch.WordTrace tailWord_1247096 prefixEnd_1247096 426906446866371976576477 := by
  unfold tailWord_1247096
  simp only [CollatzResearch.WordTrace]
  refine ⟨22742663944995826942572571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30323551926661102590096761 22742663944995826942572571)
  ·
    refine ⟨34113995917493740413858857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22742663944995826942572571 34113995917493740413858857)
    ·
      refine ⟨25585496938120305310394143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34113995917493740413858857 25585496938120305310394143)
      ·
        refine ⟨38378245407180457965591215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25585496938120305310394143 38378245407180457965591215)
        ·
          refine ⟨57567368110770686948386823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38378245407180457965591215 57567368110770686948386823)
          ·
            refine ⟨86351052166156030422580235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57567368110770686948386823 86351052166156030422580235)
            ·
              refine ⟨129526578249234045633870353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86351052166156030422580235 129526578249234045633870353)
              ·
                refine ⟨97144933686925534225402765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129526578249234045633870353 97144933686925534225402765)
                ·
                  refine ⟨36429350132597075334526037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97144933686925534225402765 36429350132597075334526037)
                  ·
                    refine ⟨426906446866371976576477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36429350132597075334526037 426906446866371976576477)
                    ·
                      rfl

theorem cell22_1247096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_1247096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1247096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1247096 prefixEnd_1247096 := by exact prefixLift 1247096
  have htrace : WordTrace (prefixWord ++ tailWord_1247096) baseStart_1247096 baseEnd_1247096 := by
    simpa [prefixWord, tailWord_1247096, baseEnd_1247096] using wordTrace_append hprefix tailTrace_1247096
  have hstable : (prefixWord ++ tailWord_1247096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247096).length < 2 ^ (prefixWord ++ tailWord_1247096).sum := by decide
  have hdescent : baseEnd_1247096 < baseStart_1247096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247132 : List Nat := [2, 2, 3, 3, 1, 1, 3, 1, 3, 3]
def baseStart_1247132 : Nat := 118140960795 + 1247132 * 2 ^ 59
def prefixEnd_1247132 : Nat := 4983230072969 + 3 ^ 40 * 1247132 * 2
def baseEnd_1247132 : Nat := 426918770402079882676367

theorem tailTrace_1247132 : CollatzResearch.WordTrace tailWord_1247132 prefixEnd_1247132 426918770402079882676367 := by
  unfold tailWord_1247132
  simp only [CollatzResearch.WordTrace]
  refine ⟨22743320458930616016727825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30324427278574154688970433 22743320458930616016727825)
  ·
    refine ⟨17057490344197962012545869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22743320458930616016727825 17057490344197962012545869)
    ·
      refine ⟨6396558879074235754704701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17057490344197962012545869 6396558879074235754704701)
      ·
        refine ⟨2398709579652838408014263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6396558879074235754704701 2398709579652838408014263)
        ·
          refine ⟨3598064369479257612021395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2398709579652838408014263 3598064369479257612021395)
          ·
            refine ⟨5397096554218886418032093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3598064369479257612021395 5397096554218886418032093)
            ·
              refine ⟨2023911207832082406762035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5397096554218886418032093 2023911207832082406762035)
              ·
                refine ⟨3035866811748123610143053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2023911207832082406762035 3035866811748123610143053)
                ·
                  refine ⟨1138450054405546353803645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3035866811748123610143053 1138450054405546353803645)
                  ·
                    refine ⟨426918770402079882676367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1138450054405546353803645 426918770402079882676367)
                    ·
                      rfl

theorem cell22_1247132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_1247132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1247132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1247132 prefixEnd_1247132 := by exact prefixLift 1247132
  have htrace : WordTrace (prefixWord ++ tailWord_1247132) baseStart_1247132 baseEnd_1247132 := by
    simpa [prefixWord, tailWord_1247132, baseEnd_1247132] using wordTrace_append hprefix tailTrace_1247132
  have hstable : (prefixWord ++ tailWord_1247132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247132).length < 2 ^ (prefixWord ++ tailWord_1247132).sum := by decide
  have hdescent : baseEnd_1247132 < baseStart_1247132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247239 : List Nat := [1, 1, 4, 3, 1, 4, 1, 2, 2, 3]
def baseStart_1247239 : Nat := 118140960795 + 1247239 * 2 ^ 59
def prefixEnd_1247239 : Nat := 4983230072969 + 3 ^ 40 * 1247239 * 2
def baseEnd_1247239 : Nat := 426955398688767270251039

theorem tailTrace_1247239 : CollatzResearch.WordTrace tailWord_1247239 prefixEnd_1247239 426955398688767270251039 := by
  unfold tailWord_1247239
  simp only [CollatzResearch.WordTrace]
  refine ⟨45490543528473589307600771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30327029018982392871733847 45490543528473589307600771)
  ·
    refine ⟨68235815292710383961401157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45490543528473589307600771 68235815292710383961401157)
    ·
      refine ⟨12794215367383196992762717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68235815292710383961401157 12794215367383196992762717)
      ·
        refine ⟨4797830762768698872286019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12794215367383196992762717 4797830762768698872286019)
        ·
          refine ⟨7196746144153048308429029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4797830762768698872286019 7196746144153048308429029)
          ·
            refine ⟨1349389902028696557830443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7196746144153048308429029 1349389902028696557830443)
            ·
              refine ⟨2024084853043044836745665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1349389902028696557830443 2024084853043044836745665)
              ·
                refine ⟨1518063639782283627559249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2024084853043044836745665 1518063639782283627559249)
                ·
                  refine ⟨1138547729836712720669437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1518063639782283627559249 1138547729836712720669437)
                  ·
                    refine ⟨426955398688767270251039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1138547729836712720669437 426955398688767270251039)
                    ·
                      rfl

theorem cell22_1247239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_1247239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1247239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1247239 prefixEnd_1247239 := by exact prefixLift 1247239
  have htrace : WordTrace (prefixWord ++ tailWord_1247239) baseStart_1247239 baseEnd_1247239 := by
    simpa [prefixWord, tailWord_1247239, baseEnd_1247239] using wordTrace_append hprefix tailTrace_1247239
  have hstable : (prefixWord ++ tailWord_1247239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247239).length < 2 ^ (prefixWord ++ tailWord_1247239).sum := by decide
  have hdescent : baseEnd_1247239 < baseStart_1247239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247340 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 3, 5]
def baseStart_1247340 : Nat := 118140960795 + 1247340 * 2 ^ 59
def prefixEnd_1247340 : Nat := 4983230072969 + 3 ^ 40 * 1247340 * 2
def baseEnd_1247340 : Nat := 426989973052836673475729

theorem tailTrace_1247340 : CollatzResearch.WordTrace tailWord_1247340 prefixEnd_1247340 426989973052836673475729 := by
  unfold tailWord_1247340
  simp only [CollatzResearch.WordTrace]
  refine ⟨22747113650553841778513737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30329484867405122371351649 22747113650553841778513737)
  ·
    refine ⟨17060335237915381333885303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22747113650553841778513737 17060335237915381333885303)
    ·
      refine ⟨25590502856873072000827955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17060335237915381333885303 25590502856873072000827955)
      ·
        refine ⟨38385754285309608001241933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25590502856873072000827955 38385754285309608001241933)
        ·
          refine ⟨14394657856991103000465725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38385754285309608001241933 14394657856991103000465725)
          ·
            refine ⟨5397996696371663625174647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14394657856991103000465725 5397996696371663625174647)
            ·
              refine ⟨8096995044557495437761971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5397996696371663625174647 8096995044557495437761971)
              ·
                refine ⟨12145492566836243156642957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8096995044557495437761971 12145492566836243156642957)
                ·
                  refine ⟨4554559712563591183741109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12145492566836243156642957 4554559712563591183741109)
                  ·
                    refine ⟨426989973052836673475729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4554559712563591183741109 426989973052836673475729)
                    ·
                      rfl

theorem cell22_1247340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_1247340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1247340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1247340 prefixEnd_1247340 := by exact prefixLift 1247340
  have htrace : WordTrace (prefixWord ++ tailWord_1247340) baseStart_1247340 baseEnd_1247340 := by
    simpa [prefixWord, tailWord_1247340, baseEnd_1247340] using wordTrace_append hprefix tailTrace_1247340
  have hstable : (prefixWord ++ tailWord_1247340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247340).length < 2 ^ (prefixWord ++ tailWord_1247340).sum := by decide
  have hdescent : baseEnd_1247340 < baseStart_1247340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247344 : List Nat := [2, 1, 1, 1, 5, 3, 3, 1, 1, 4]
def baseStart_1247344 : Nat := 118140960795 + 1247344 * 2 ^ 59
def prefixEnd_1247344 : Nat := 4983230072969 + 3 ^ 40 * 1247344 * 2
def baseEnd_1247344 : Nat := 426991342334581996375717

theorem tailTrace_1247344 : CollatzResearch.WordTrace tailWord_1247344 prefixEnd_1247344 426991342334581996375717 := by
  unfold tailWord_1247344
  simp only [CollatzResearch.WordTrace]
  refine ⟨22747186596546596120086543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30329582128728794826782057 22747186596546596120086543)
  ·
    refine ⟨34120779894819894180129815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22747186596546596120086543 34120779894819894180129815)
    ·
      refine ⟨51181169842229841270194723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34120779894819894180129815 51181169842229841270194723)
      ·
        refine ⟨76771754763344761905292085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51181169842229841270194723 76771754763344761905292085)
        ·
          refine ⟨7197352009063571428621133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76771754763344761905292085 7197352009063571428621133)
          ·
            refine ⟨2699007003398839285732925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7197352009063571428621133 2699007003398839285732925)
            ·
              refine ⟨1012127626274564732149847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2699007003398839285732925 1012127626274564732149847)
              ·
                refine ⟨1518191439411847098224771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1012127626274564732149847 1518191439411847098224771)
                ·
                  refine ⟨2277287159117770647337157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1518191439411847098224771 2277287159117770647337157)
                  ·
                    refine ⟨426991342334581996375717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2277287159117770647337157 426991342334581996375717)
                    ·
                      rfl

theorem cell22_1247344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 1, 4].length) (baseStart_1247344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1247344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1247344 prefixEnd_1247344 := by exact prefixLift 1247344
  have htrace : WordTrace (prefixWord ++ tailWord_1247344) baseStart_1247344 baseEnd_1247344 := by
    simpa [prefixWord, tailWord_1247344, baseEnd_1247344] using wordTrace_append hprefix tailTrace_1247344
  have hstable : (prefixWord ++ tailWord_1247344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247344).length < 2 ^ (prefixWord ++ tailWord_1247344).sum := by decide
  have hdescent : baseEnd_1247344 < baseStart_1247344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247374 : List Nat := [4, 1, 1, 3, 3, 1, 2, 1, 1, 5]
def baseStart_1247374 : Nat := 118140960795 + 1247374 * 2 ^ 59
def prefixEnd_1247374 : Nat := 4983230072969 + 3 ^ 40 * 1247374 * 2
def baseEnd_1247374 : Nat := 427001611947671918125625

theorem tailTrace_1247374 : CollatzResearch.WordTrace tailWord_1247374 prefixEnd_1247374 427001611947671918125625 := by
  unfold tailWord_1247374
  simp only [CollatzResearch.WordTrace]
  refine ⟨5686933422873063420470647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30330311588656338242510117 5686933422873063420470647)
  ·
    refine ⟨8530400134309595130705971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5686933422873063420470647 8530400134309595130705971)
    ·
      refine ⟨12795600201464392696058957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8530400134309595130705971 12795600201464392696058957)
      ·
        refine ⟨4798350075549147261022109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12795600201464392696058957 4798350075549147261022109)
        ·
          refine ⟨1799381278330930222883291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4798350075549147261022109 1799381278330930222883291)
          ·
            refine ⟨2699071917496395334324937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1799381278330930222883291 2699071917496395334324937)
            ·
              refine ⟨2024303938122296500743703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2699071917496395334324937 2024303938122296500743703)
              ·
                refine ⟨3036455907183444751115555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2024303938122296500743703 3036455907183444751115555)
                ·
                  refine ⟨4554683860775167126673333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3036455907183444751115555 4554683860775167126673333)
                  ·
                    refine ⟨427001611947671918125625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4554683860775167126673333 427001611947671918125625)
                    ·
                      rfl

theorem cell22_1247374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_1247374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1247374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1247374 prefixEnd_1247374 := by exact prefixLift 1247374
  have htrace : WordTrace (prefixWord ++ tailWord_1247374) baseStart_1247374 baseEnd_1247374 := by
    simpa [prefixWord, tailWord_1247374, baseEnd_1247374] using wordTrace_append hprefix tailTrace_1247374
  have hstable : (prefixWord ++ tailWord_1247374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247374).length < 2 ^ (prefixWord ++ tailWord_1247374).sum := by decide
  have hdescent : baseEnd_1247374 < baseStart_1247374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247389 : List Nat := [1, 4, 2, 1, 1, 5, 1, 1, 2, 4]
def baseStart_1247389 : Nat := 118140960795 + 1247389 * 2 ^ 59
def prefixEnd_1247389 : Nat := 4983230072969 + 3 ^ 40 * 1247389 * 2
def baseEnd_1247389 : Nat := 427006746754216879000579

theorem tailTrace_1247389 : CollatzResearch.WordTrace tailWord_1247389 prefixEnd_1247389 427006746754216879000579 := by
  unfold tailWord_1247389
  simp only [CollatzResearch.WordTrace]
  refine ⟨45496014477930164925561221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30330676318620109950374147 45496014477930164925561221)
  ·
    refine ⟨8530502714611905923542729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45496014477930164925561221 8530502714611905923542729)
    ·
      refine ⟨6397877035958929442657047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8530502714611905923542729 6397877035958929442657047)
      ·
        refine ⟨9596815553938394163985571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6397877035958929442657047 9596815553938394163985571)
        ·
          refine ⟨14395223330907591245978357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9596815553938394163985571 14395223330907591245978357)
          ·
            refine ⟨1349552187272586679310471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14395223330907591245978357 1349552187272586679310471)
            ·
              refine ⟨2024328280908880018965707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1349552187272586679310471 2024328280908880018965707)
              ·
                refine ⟨3036492421363320028448561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2024328280908880018965707 3036492421363320028448561)
                ·
                  refine ⟨2277369316022490021336421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3036492421363320028448561 2277369316022490021336421)
                  ·
                    refine ⟨427006746754216879000579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2277369316022490021336421 427006746754216879000579)
                    ·
                      rfl

theorem cell22_1247389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_1247389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1247389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1247389 prefixEnd_1247389 := by exact prefixLift 1247389
  have htrace : WordTrace (prefixWord ++ tailWord_1247389) baseStart_1247389 baseEnd_1247389 := by
    simpa [prefixWord, tailWord_1247389, baseEnd_1247389] using wordTrace_append hprefix tailTrace_1247389
  have hstable : (prefixWord ++ tailWord_1247389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247389).length < 2 ^ (prefixWord ++ tailWord_1247389).sum := by decide
  have hdescent : baseEnd_1247389 < baseStart_1247389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247419 : List Nat := [1, 1, 1, 1, 1, 2, 5, 6, 1, 3]
def baseStart_1247419 : Nat := 118140960795 + 1247419 * 2 ^ 59
def prefixEnd_1247419 : Nat := 4983230072969 + 3 ^ 40 * 1247419 * 2
def baseEnd_1247419 : Nat := 427017016367306800750487

theorem tailTrace_1247419 : CollatzResearch.WordTrace tailWord_1247419 prefixEnd_1247419 427017016367306800750487 := by
  unfold tailWord_1247419
  simp only [CollatzResearch.WordTrace]
  refine ⟨45497108667821480049153311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30331405778547653366102207 45497108667821480049153311)
  ·
    refine ⟨68245663001732220073729967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45497108667821480049153311 68245663001732220073729967)
    ·
      refine ⟨102368494502598330110594951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68245663001732220073729967 102368494502598330110594951)
      ·
        refine ⟨153552741753897495165892427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102368494502598330110594951 153552741753897495165892427)
        ·
          refine ⟨230329112630846242748838641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153552741753897495165892427 230329112630846242748838641)
          ·
            refine ⟨172746834473134682061628981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230329112630846242748838641 172746834473134682061628981)
            ·
              refine ⟨16195015731856376443277717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 172746834473134682061628981 16195015731856376443277717)
              ·
                refine ⟨759141362430767645778643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16195015731856376443277717 759141362430767645778643)
                ·
                  refine ⟨1138712043646151468667965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 759141362430767645778643 1138712043646151468667965)
                  ·
                    refine ⟨427017016367306800750487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1138712043646151468667965 427017016367306800750487)
                    ·
                      rfl

theorem cell22_1247419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6, 1, 3].length) (baseStart_1247419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1247419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1247419 prefixEnd_1247419 := by exact prefixLift 1247419
  have htrace : WordTrace (prefixWord ++ tailWord_1247419) baseStart_1247419 baseEnd_1247419 := by
    simpa [prefixWord, tailWord_1247419, baseEnd_1247419] using wordTrace_append hprefix tailTrace_1247419
  have hstable : (prefixWord ++ tailWord_1247419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247419).length < 2 ^ (prefixWord ++ tailWord_1247419).sum := by decide
  have hdescent : baseEnd_1247419 < baseStart_1247419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247453 : List Nat := [1, 4, 3, 2, 1, 1, 3, 3, 1, 3]
def baseStart_1247453 : Nat := 118140960795 + 1247453 * 2 ^ 59
def prefixEnd_1247453 : Nat := 4983230072969 + 3 ^ 40 * 1247453 * 2
def baseEnd_1247453 : Nat := 427028655262142045400383

theorem tailTrace_1247453 : CollatzResearch.WordTrace tailWord_1247453 prefixEnd_1247453 427028655262142045400383 := by
  unfold tailWord_1247453
  simp only [CollatzResearch.WordTrace]
  refine ⟨45498348749698303855891013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30332232499798869237260675 45498348749698303855891013)
  ·
    refine ⟨8530940390568431972979565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45498348749698303855891013 8530940390568431972979565)
    ·
      refine ⟨3199102646463161989867337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8530940390568431972979565 3199102646463161989867337)
      ·
        refine ⟨2399326984847371492400503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3199102646463161989867337 2399326984847371492400503)
        ·
          refine ⟨3598990477271057238600755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2399326984847371492400503 3598990477271057238600755)
          ·
            refine ⟨5398485715906585857901133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3598990477271057238600755 5398485715906585857901133)
            ·
              refine ⟨2024432143464969696712925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5398485715906585857901133 2024432143464969696712925)
              ·
                refine ⟨759162053799363636267347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2024432143464969696712925 759162053799363636267347)
                ·
                  refine ⟨1138743080699045454401021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 759162053799363636267347 1138743080699045454401021)
                  ·
                    refine ⟨427028655262142045400383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1138743080699045454401021 427028655262142045400383)
                    ·
                      rfl

theorem cell22_1247453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_1247453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1247453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1247453 prefixEnd_1247453 := by exact prefixLift 1247453
  have htrace : WordTrace (prefixWord ++ tailWord_1247453) baseStart_1247453 baseEnd_1247453 := by
    simpa [prefixWord, tailWord_1247453, baseEnd_1247453] using wordTrace_append hprefix tailTrace_1247453
  have hstable : (prefixWord ++ tailWord_1247453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247453).length < 2 ^ (prefixWord ++ tailWord_1247453).sum := by decide
  have hdescent : baseEnd_1247453 < baseStart_1247453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247496 : List Nat := [2, 1, 3, 2, 3, 3, 1, 2, 1, 4]
def baseStart_1247496 : Nat := 118140960795 + 1247496 * 2 ^ 59
def prefixEnd_1247496 : Nat := 4983230072969 + 3 ^ 40 * 1247496 * 2
def baseEnd_1247496 : Nat := 427043375040904266575251

theorem tailTrace_1247496 : CollatzResearch.WordTrace tailWord_1247496 prefixEnd_1247496 427043375040904266575251 := by
  unfold tailWord_1247496
  simp only [CollatzResearch.WordTrace]
  refine ⟨22749958544271261099853171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30333278059028348133137561 22749958544271261099853171)
  ·
    refine ⟨34124937816406891649779757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22749958544271261099853171 34124937816406891649779757)
    ·
      refine ⟨12796851681152584368667409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34124937816406891649779757 12796851681152584368667409)
      ·
        refine ⟨9597638760864438276500557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12796851681152584368667409 9597638760864438276500557)
        ·
          refine ⟨3599114535324164353687709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9597638760864438276500557 3599114535324164353687709)
          ·
            refine ⟨1349667950746561632632891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3599114535324164353687709 1349667950746561632632891)
            ·
              refine ⟨2024501926119842448949337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1349667950746561632632891 2024501926119842448949337)
              ·
                refine ⟨1518376444589881836712003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2024501926119842448949337 1518376444589881836712003)
                ·
                  refine ⟨2277564666884822755068005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1518376444589881836712003 2277564666884822755068005)
                  ·
                    refine ⟨427043375040904266575251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2277564666884822755068005 427043375040904266575251)
                    ·
                      rfl

theorem cell22_1247496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_1247496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1247496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1247496 prefixEnd_1247496 := by exact prefixLift 1247496
  have htrace : WordTrace (prefixWord ++ tailWord_1247496) baseStart_1247496 baseEnd_1247496 := by
    simpa [prefixWord, tailWord_1247496, baseEnd_1247496] using wordTrace_append hprefix tailTrace_1247496
  have hstable : (prefixWord ++ tailWord_1247496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247496).length < 2 ^ (prefixWord ++ tailWord_1247496).sum := by decide
  have hdescent : baseEnd_1247496 < baseStart_1247496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247522 : List Nat := [3, 3, 1, 1, 3, 11]
def baseStart_1247522 : Nat := 118140960795 + 1247522 * 2 ^ 59
def prefixEnd_1247522 : Nat := 4983230072969 + 3 ^ 40 * 1247522 * 2
def baseEnd_1247522 : Nat := 5272250313237640313891

theorem tailTrace_1247522 : CollatzResearch.WordTrace tailWord_1247522 prefixEnd_1247522 5272250313237640313891 := by
  unfold tailWord_1247522
  simp only [CollatzResearch.WordTrace]
  refine ⟨11375216346612082160038205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30333910257632219093435213 11375216346612082160038205)
  ·
    refine ⟨4265706129979530810014327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11375216346612082160038205 4265706129979530810014327)
    ·
      refine ⟨6398559194969296215021491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4265706129979530810014327 6398559194969296215021491)
      ·
        refine ⟨9597838792453944322532237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6398559194969296215021491 9597838792453944322532237)
        ·
          refine ⟨3599189547170229120949589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9597838792453944322532237 3599189547170229120949589)
          ·
            refine ⟨5272250313237640313891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3599189547170229120949589 5272250313237640313891)
            ·
              rfl

theorem cell22_1247522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 11].length) (baseStart_1247522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1247522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1247522 prefixEnd_1247522 := by exact prefixLift 1247522
  have htrace : WordTrace (prefixWord ++ tailWord_1247522) baseStart_1247522 baseEnd_1247522 := by
    simpa [prefixWord, tailWord_1247522, baseEnd_1247522] using wordTrace_append hprefix tailTrace_1247522
  have hstable : (prefixWord ++ tailWord_1247522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247522).length < 2 ^ (prefixWord ++ tailWord_1247522).sum := by decide
  have hdescent : baseEnd_1247522 < baseStart_1247522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247524 : List Nat := [2, 3, 1, 3, 1, 2, 2, 2, 2, 4]
def baseStart_1247524 : Nat := 118140960795 + 1247524 * 2 ^ 59
def prefixEnd_1247524 : Nat := 4983230072969 + 3 ^ 40 * 1247524 * 2
def baseEnd_1247524 : Nat := 427052960013121526875165

theorem tailTrace_1247524 : CollatzResearch.WordTrace tailWord_1247524 prefixEnd_1247524 427052960013121526875165 := by
  unfold tailWord_1247524
  simp only [CollatzResearch.WordTrace]
  refine ⟨22750469166220541490862813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30333958888294055321150417 22750469166220541490862813)
  ·
    refine ⟨8531425937332703059073555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22750469166220541490862813 8531425937332703059073555)
    ·
      refine ⟨12797138905999054588610333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8531425937332703059073555 12797138905999054588610333)
      ·
        refine ⟨4798927089749645470728875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12797138905999054588610333 4798927089749645470728875)
        ·
          refine ⟨7198390634624468206093313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4798927089749645470728875 7198390634624468206093313)
          ·
            refine ⟨5398792975968351154569985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7198390634624468206093313 5398792975968351154569985)
            ·
              refine ⟨4049094731976263365927489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5398792975968351154569985 4049094731976263365927489)
              ·
                refine ⟨3036821048982197524445617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4049094731976263365927489 3036821048982197524445617)
                ·
                  refine ⟨2277615786736648143334213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3036821048982197524445617 2277615786736648143334213)
                  ·
                    refine ⟨427052960013121526875165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2277615786736648143334213 427052960013121526875165)
                    ·
                      rfl

theorem cell22_1247524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_1247524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1247524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1247524 prefixEnd_1247524 := by exact prefixLift 1247524
  have htrace : WordTrace (prefixWord ++ tailWord_1247524) baseStart_1247524 baseEnd_1247524 := by
    simpa [prefixWord, tailWord_1247524, baseEnd_1247524] using wordTrace_append hprefix tailTrace_1247524
  have hstable : (prefixWord ++ tailWord_1247524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247524).length < 2 ^ (prefixWord ++ tailWord_1247524).sum := by decide
  have hdescent : baseEnd_1247524 < baseStart_1247524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247584 : List Nat := [2, 1, 1, 3, 5, 1, 1, 1, 7]
def baseStart_1247584 : Nat := 118140960795 + 1247584 * 2 ^ 59
def prefixEnd_1247584 : Nat := 4983230072969 + 3 ^ 40 * 1247584 * 2
def baseEnd_1247584 : Nat := 142357833079767123458327

theorem tailTrace_1247584 : CollatzResearch.WordTrace tailWord_1247584 prefixEnd_1247584 142357833079767123458327 := by
  unfold tailWord_1247584
  simp only [CollatzResearch.WordTrace]
  refine ⟨22751563356111856614454903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30335417808149142152606537 22751563356111856614454903)
  ·
    refine ⟨34127345034167784921682355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22751563356111856614454903 34127345034167784921682355)
    ·
      refine ⟨51191017551251677382523533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34127345034167784921682355 51191017551251677382523533)
      ·
        refine ⟨19196631581719379018446325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51191017551251677382523533 19196631581719379018446325)
        ·
          refine ⟨1799684210786191782979343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19196631581719379018446325 1799684210786191782979343)
          ·
            refine ⟨2699526316179287674469015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1799684210786191782979343 2699526316179287674469015)
            ·
              refine ⟨4049289474268931511703523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2699526316179287674469015 4049289474268931511703523)
              ·
                refine ⟨6073934211403397267555285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4049289474268931511703523 6073934211403397267555285)
                ·
                  refine ⟨142357833079767123458327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6073934211403397267555285 142357833079767123458327)
                  ·
                    rfl

theorem cell22_1247584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 7].length) (baseStart_1247584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1247584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1247584 prefixEnd_1247584 := by exact prefixLift 1247584
  have htrace : WordTrace (prefixWord ++ tailWord_1247584) baseStart_1247584 baseEnd_1247584 := by
    simpa [prefixWord, tailWord_1247584, baseEnd_1247584] using wordTrace_append hprefix tailTrace_1247584
  have hstable : (prefixWord ++ tailWord_1247584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247584).length < 2 ^ (prefixWord ++ tailWord_1247584).sum := by decide
  have hdescent : baseEnd_1247584 < baseStart_1247584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247612 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 8]
def baseStart_1247612 : Nat := 118140960795 + 1247612 * 2 ^ 59
def prefixEnd_1247612 : Nat := 4983230072969 + 3 ^ 40 * 1247612 * 2
def baseEnd_1247612 : Nat := 142361028070506210224965

theorem tailTrace_1247612 : CollatzResearch.WordTrace tailWord_1247612 prefixEnd_1247612 142361028070506210224965 := by
  unfold tailWord_1247612
  simp only [CollatzResearch.WordTrace]
  refine ⟨22752073978061137005464545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30336098637414849340619393 22752073978061137005464545)
  ·
    refine ⟨17064055483545852754098409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22752073978061137005464545 17064055483545852754098409)
    ·
      refine ⟨12798041612659389565573807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17064055483545852754098409 12798041612659389565573807)
      ·
        refine ⟨19197062418989084348360711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12798041612659389565573807 19197062418989084348360711)
        ·
          refine ⟨28795593628483626522541067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19197062418989084348360711 28795593628483626522541067)
          ·
            refine ⟨43193390442725439783811601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28795593628483626522541067 43193390442725439783811601)
            ·
              refine ⟨32395042832044079837858701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43193390442725439783811601 32395042832044079837858701)
              ·
                refine ⟨12148141062016529939197013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32395042832044079837858701 12148141062016529939197013)
                ·
                  refine ⟨142361028070506210224965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12148141062016529939197013 142361028070506210224965)
                  ·
                    rfl

theorem cell22_1247612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 8].length) (baseStart_1247612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1247612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1247612 prefixEnd_1247612 := by exact prefixLift 1247612
  have htrace : WordTrace (prefixWord ++ tailWord_1247612) baseStart_1247612 baseEnd_1247612 := by
    simpa [prefixWord, tailWord_1247612, baseEnd_1247612] using wordTrace_append hprefix tailTrace_1247612
  have hstable : (prefixWord ++ tailWord_1247612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247612).length < 2 ^ (prefixWord ++ tailWord_1247612).sum := by decide
  have hdescent : baseEnd_1247612 < baseStart_1247612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247676 : List Nat := [2, 2, 2, 4, 1, 1, 1, 3, 2, 4]
def baseStart_1247676 : Nat := 118140960795 + 1247676 * 2 ^ 59
def prefixEnd_1247676 : Nat := 4983230072969 + 3 ^ 40 * 1247676 * 2
def baseEnd_1247676 : Nat := 427104992719443797074699

theorem tailTrace_1247676 : CollatzResearch.WordTrace tailWord_1247676 prefixEnd_1247676 427104992719443797074699 := by
  unfold tailWord_1247676
  simp only [CollatzResearch.WordTrace]
  refine ⟨22753241113945206470629441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30337654818593608627505921 22753241113945206470629441)
  ·
    refine ⟨17064930835458904852972081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22753241113945206470629441 17064930835458904852972081)
    ·
      refine ⟨12798698126594178639729061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17064930835458904852972081 12798698126594178639729061)
      ·
        refine ⟨2399755898736408494949199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12798698126594178639729061 2399755898736408494949199)
        ·
          refine ⟨3599633848104612742423799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2399755898736408494949199 3599633848104612742423799)
          ·
            refine ⟨5399450772156919113635699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3599633848104612742423799 5399450772156919113635699)
            ·
              refine ⟨8099176158235378670453549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5399450772156919113635699 8099176158235378670453549)
              ·
                refine ⟨3037191059338267001420081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8099176158235378670453549 3037191059338267001420081)
                ·
                  refine ⟨2277893294503700251065061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3037191059338267001420081 2277893294503700251065061)
                  ·
                    refine ⟨427104992719443797074699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2277893294503700251065061 427104992719443797074699)
                    ·
                      rfl

theorem cell22_1247676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_1247676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1247676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1247676 prefixEnd_1247676 := by exact prefixLift 1247676
  have htrace : WordTrace (prefixWord ++ tailWord_1247676) baseStart_1247676 baseEnd_1247676 := by
    simpa [prefixWord, tailWord_1247676, baseEnd_1247676] using wordTrace_append hprefix tailTrace_1247676
  have hstable : (prefixWord ++ tailWord_1247676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247676).length < 2 ^ (prefixWord ++ tailWord_1247676).sum := by decide
  have hdescent : baseEnd_1247676 < baseStart_1247676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247706 : List Nat := [3, 1, 1, 2, 3, 1, 2, 3, 3, 3]
def baseStart_1247706 : Nat := 118140960795 + 1247706 * 2 ^ 59
def prefixEnd_1247706 : Nat := 4983230072969 + 3 ^ 40 * 1247706 * 2
def baseEnd_1247706 : Nat := 427115262332533718824607

theorem tailTrace_1247706 : CollatzResearch.WordTrace tailWord_1247706 prefixEnd_1247706 427115262332533718824607 := by
  unfold tailWord_1247706
  simp only [CollatzResearch.WordTrace]
  refine ⟨11376894104445432016212743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30338384278521152043233981 11376894104445432016212743)
  ·
    refine ⟨17065341156668148024319115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11376894104445432016212743 17065341156668148024319115)
    ·
      refine ⟨25598011735002222036478673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17065341156668148024319115 25598011735002222036478673)
      ·
        refine ⟨19198508801251666527359005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25598011735002222036478673 19198508801251666527359005)
        ·
          refine ⟨7199440800469374947759627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19198508801251666527359005 7199440800469374947759627)
          ·
            refine ⟨10799161200704062421639441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7199440800469374947759627 10799161200704062421639441)
            ·
              refine ⟨8099370900528046816229581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10799161200704062421639441 8099370900528046816229581)
              ·
                refine ⟨3037264087698017556086093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8099370900528046816229581 3037264087698017556086093)
                ·
                  refine ⟨1138974032886756583532285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3037264087698017556086093 1138974032886756583532285)
                  ·
                    refine ⟨427115262332533718824607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1138974032886756583532285 427115262332533718824607)
                    ·
                      rfl

theorem cell22_1247706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 3, 3].length) (baseStart_1247706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1247706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1247706 prefixEnd_1247706 := by exact prefixLift 1247706
  have htrace : WordTrace (prefixWord ++ tailWord_1247706) baseStart_1247706 baseEnd_1247706 := by
    simpa [prefixWord, tailWord_1247706, baseEnd_1247706] using wordTrace_append hprefix tailTrace_1247706
  have hstable : (prefixWord ++ tailWord_1247706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247706).length < 2 ^ (prefixWord ++ tailWord_1247706).sum := by decide
  have hdescent : baseEnd_1247706 < baseStart_1247706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247757 : List Nat := [1, 7, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_1247757 : Nat := 118140960795 + 1247757 * 2 ^ 59
def prefixEnd_1247757 : Nat := 4983230072969 + 3 ^ 40 * 1247757 * 2
def baseEnd_1247757 : Nat := 427132720674786585799451

theorem tailTrace_1247757 : CollatzResearch.WordTrace tailWord_1247757 prefixEnd_1247757 427132720674786585799451 := by
  unfold tailWord_1247757
  simp only [CollatzResearch.WordTrace]
  refine ⟨45509436540596963774957525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30339624360397975849971683 45509436540596963774957525)
  ·
    refine ⟨1066627418920241338475567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 45509436540596963774957525 1066627418920241338475567)
    ·
      refine ⟨1599941128380362007713351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1066627418920241338475567 1599941128380362007713351)
      ·
        refine ⟨2399911692570543011570027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1599941128380362007713351 2399911692570543011570027)
        ·
          refine ⟨3599867538855814517355041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2399911692570543011570027 3599867538855814517355041)
          ·
            refine ⟨2699900654141860888016281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3599867538855814517355041 2699900654141860888016281)
            ·
              refine ⟨2024925490606395666012211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2699900654141860888016281 2024925490606395666012211)
              ·
                refine ⟨3037388235909593499018317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2024925490606395666012211 3037388235909593499018317)
                ·
                  refine ⟨1139020588466097562131869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3037388235909593499018317 1139020588466097562131869)
                  ·
                    refine ⟨427132720674786585799451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1139020588466097562131869 427132720674786585799451)
                    ·
                      rfl

theorem cell22_1247757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_1247757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1247757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1247757 prefixEnd_1247757 := by exact prefixLift 1247757
  have htrace : WordTrace (prefixWord ++ tailWord_1247757) baseStart_1247757 baseEnd_1247757 := by
    simpa [prefixWord, tailWord_1247757, baseEnd_1247757] using wordTrace_append hprefix tailTrace_1247757
  have hstable : (prefixWord ++ tailWord_1247757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247757).length < 2 ^ (prefixWord ++ tailWord_1247757).sum := by decide
  have hdescent : baseEnd_1247757 < baseStart_1247757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247815 : List Nat := [1, 1, 4, 1, 4, 2, 3, 2, 4]
def baseStart_1247815 : Nat := 118140960795 + 1247815 * 2 ^ 59
def prefixEnd_1247815 : Nat := 4983230072969 + 3 ^ 40 * 1247815 * 2
def baseEnd_1247815 : Nat := 142384191753364589283091

theorem tailTrace_1247815 : CollatzResearch.WordTrace tailWord_1247815 prefixEnd_1247815 142384191753364589283091 := by
  unfold tailWord_1247815
  simp only [CollatzResearch.WordTrace]
  refine ⟨45511551974386839680568899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30341034649591226453712599 45511551974386839680568899)
  ·
    refine ⟨68267327961580259520853349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45511551974386839680568899 68267327961580259520853349)
    ·
      refine ⟨12800123992796298660160003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68267327961580259520853349 12800123992796298660160003)
      ·
        refine ⟨19200185989194447990240005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12800123992796298660160003 19200185989194447990240005)
        ·
          refine ⟨3600034872973958998170001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19200185989194447990240005 3600034872973958998170001)
          ·
            refine ⟨2700026154730469248627501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3600034872973958998170001 2700026154730469248627501)
            ·
              refine ⟨1012509808023925968235313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2700026154730469248627501 1012509808023925968235313)
              ·
                refine ⟨759382356017944476176485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1012509808023925968235313 759382356017944476176485)
                ·
                  refine ⟨142384191753364589283091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 759382356017944476176485 142384191753364589283091)
                  ·
                    rfl

theorem cell22_1247815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 2, 4].length) (baseStart_1247815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1247815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1247815 prefixEnd_1247815 := by exact prefixLift 1247815
  have htrace : WordTrace (prefixWord ++ tailWord_1247815) baseStart_1247815 baseEnd_1247815 := by
    simpa [prefixWord, tailWord_1247815, baseEnd_1247815] using wordTrace_append hprefix tailTrace_1247815
  have hstable : (prefixWord ++ tailWord_1247815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247815).length < 2 ^ (prefixWord ++ tailWord_1247815).sum := by decide
  have hdescent : baseEnd_1247815 < baseStart_1247815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247824 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 2, 7]
def baseStart_1247824 : Nat := 118140960795 + 1247824 * 2 ^ 59
def prefixEnd_1247824 : Nat := 4983230072969 + 3 ^ 40 * 1247824 * 2
def baseEnd_1247824 : Nat := 427155656144020744374245

theorem tailTrace_1247824 : CollatzResearch.WordTrace tailWord_1247824 prefixEnd_1247824 427155656144020744374245 := by
  unfold tailWord_1247824
  simp only [CollatzResearch.WordTrace]
  refine ⟨22755940115677117108823263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30341253487569489478431017 22755940115677117108823263)
  ·
    refine ⟨34133910173515675663234895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22755940115677117108823263 34133910173515675663234895)
    ·
      refine ⟨51200865260273513494852343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34133910173515675663234895 51200865260273513494852343)
      ·
        refine ⟨76801297890410270242278515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51200865260273513494852343 76801297890410270242278515)
        ·
          refine ⟨115201946835615405363417773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76801297890410270242278515 115201946835615405363417773)
          ·
            refine ⟨43200730063355777011281665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115201946835615405363417773 43200730063355777011281665)
            ·
              refine ⟨32400547547516832758461249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43200730063355777011281665 32400547547516832758461249)
              ·
                refine ⟨24300410660637624568845937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32400547547516832758461249 24300410660637624568845937)
                ·
                  refine ⟨18225307995478218426634453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24300410660637624568845937 18225307995478218426634453)
                  ·
                    refine ⟨427155656144020744374245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18225307995478218426634453 427155656144020744374245)
                    ·
                      rfl

theorem cell22_1247824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 2, 7].length) (baseStart_1247824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1247824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1247824 prefixEnd_1247824 := by exact prefixLift 1247824
  have htrace : WordTrace (prefixWord ++ tailWord_1247824) baseStart_1247824 baseEnd_1247824 := by
    simpa [prefixWord, tailWord_1247824, baseEnd_1247824] using wordTrace_append hprefix tailTrace_1247824
  have hstable : (prefixWord ++ tailWord_1247824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247824).length < 2 ^ (prefixWord ++ tailWord_1247824).sum := by decide
  have hdescent : baseEnd_1247824 < baseStart_1247824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247826 : List Nat := [3, 2, 2, 1, 2, 1, 4, 7]
def baseStart_1247826 : Nat := 118140960795 + 1247826 * 2 ^ 59
def prefixEnd_1247826 : Nat := 4983230072969 + 3 ^ 40 * 1247826 * 2
def baseEnd_1247826 : Nat := 47461815642765933980471

theorem tailTrace_1247826 : CollatzResearch.WordTrace tailWord_1247826 prefixEnd_1247826 47461815642765933980471 := by
  unfold tailWord_1247826
  simp only [CollatzResearch.WordTrace]
  refine ⟨11377988294336747139804833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30341302118231325706146221 11377988294336747139804833)
  ·
    refine ⟨8533491220752560354853625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11377988294336747139804833 8533491220752560354853625)
    ·
      refine ⟨6400118415564420266140219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8533491220752560354853625 6400118415564420266140219)
      ·
        refine ⟨9600177623346630399210329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6400118415564420266140219 9600177623346630399210329)
        ·
          refine ⟨7200133217509972799407747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9600177623346630399210329 7200133217509972799407747)
          ·
            refine ⟨10800199826264959199111621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7200133217509972799407747 10800199826264959199111621)
            ·
              refine ⟨2025037467424679849833429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10800199826264959199111621 2025037467424679849833429)
              ·
                refine ⟨47461815642765933980471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2025037467424679849833429 47461815642765933980471)
                ·
                  rfl

theorem cell22_1247826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 7].length) (baseStart_1247826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1247826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1247826 prefixEnd_1247826 := by exact prefixLift 1247826
  have htrace : WordTrace (prefixWord ++ tailWord_1247826) baseStart_1247826 baseEnd_1247826 := by
    simpa [prefixWord, tailWord_1247826, baseEnd_1247826] using wordTrace_append hprefix tailTrace_1247826
  have hstable : (prefixWord ++ tailWord_1247826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247826).length < 2 ^ (prefixWord ++ tailWord_1247826).sum := by decide
  have hdescent : baseEnd_1247826 < baseStart_1247826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247933 : List Nat := [1, 4, 1, 2, 1, 4, 2, 1, 6]
def baseStart_1247933 : Nat := 118140960795 + 1247933 * 2 ^ 59
def prefixEnd_1247933 : Nat := 4983230072969 + 3 ^ 40 * 1247933 * 2
def baseEnd_1247933 : Nat := 142397656357193597799637

theorem tailTrace_1247933 : CollatzResearch.WordTrace tailWord_1247933 prefixEnd_1247933 142397656357193597799637 := by
  unfold tailWord_1247933
  simp only [CollatzResearch.WordTrace]
  refine ⟨45515855787959345833364453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30343903858639563888909635 45515855787959345833364453)
  ·
    refine ⟨8534222960242377343755835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45515855787959345833364453 8534222960242377343755835)
    ·
      refine ⟨12801334440363566015633753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8534222960242377343755835 12801334440363566015633753)
      ·
        refine ⟨9601000830272674511725315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12801334440363566015633753 9601000830272674511725315)
        ·
          refine ⟨14401501245409011767587973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9601000830272674511725315 14401501245409011767587973)
          ·
            refine ⟨2700281483514189706422745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14401501245409011767587973 2700281483514189706422745)
            ·
              refine ⟨2025211112635642279817059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2700281483514189706422745 2025211112635642279817059)
              ·
                refine ⟨3037816668953463419725589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2025211112635642279817059 3037816668953463419725589)
                ·
                  refine ⟨142397656357193597799637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3037816668953463419725589 142397656357193597799637)
                  ·
                    rfl

theorem cell22_1247933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_1247933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1247933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1247933 prefixEnd_1247933 := by exact prefixLift 1247933
  have htrace : WordTrace (prefixWord ++ tailWord_1247933) baseStart_1247933 baseEnd_1247933 := by
    simpa [prefixWord, tailWord_1247933, baseEnd_1247933] using wordTrace_append hprefix tailTrace_1247933
  have hstable : (prefixWord ++ tailWord_1247933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247933).length < 2 ^ (prefixWord ++ tailWord_1247933).sum := by decide
  have hdescent : baseEnd_1247933 < baseStart_1247933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247961 : List Nat := [1, 2, 1, 2, 3, 2, 3, 8]
def baseStart_1247961 : Nat := 118140960795 + 1247961 * 2 ^ 59
def prefixEnd_1247961 : Nat := 4983230072969 + 3 ^ 40 * 1247961 * 2
def baseEnd_1247961 : Nat := 47466950449310894855425

theorem tailTrace_1247961 : CollatzResearch.WordTrace tailWord_1247961 prefixEnd_1247961 47466950449310894855425 := by
  unfold tailWord_1247961
  simp only [CollatzResearch.WordTrace]
  refine ⟨45516877031857906615383737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30344584687905271076922491 45516877031857906615383737)
  ·
    refine ⟨34137657773893429961537803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45516877031857906615383737 34137657773893429961537803)
    ·
      refine ⟨51206486660840144942306705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34137657773893429961537803 51206486660840144942306705)
      ·
        refine ⟨38404864995630108706730029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51206486660840144942306705 38404864995630108706730029)
        ·
          refine ⟨14401824373361290765023761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38404864995630108706730029 14401824373361290765023761)
          ·
            refine ⟨10801368280020968073767821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14401824373361290765023761 10801368280020968073767821)
            ·
              refine ⟨4050513105007863027662933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10801368280020968073767821 4050513105007863027662933)
              ·
                refine ⟨47466950449310894855425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4050513105007863027662933 47466950449310894855425)
                ·
                  rfl

theorem cell22_1247961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 8].length) (baseStart_1247961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1247961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1247961 prefixEnd_1247961 := by exact prefixLift 1247961
  have htrace : WordTrace (prefixWord ++ tailWord_1247961) baseStart_1247961 baseEnd_1247961 := by
    simpa [prefixWord, tailWord_1247961, baseEnd_1247961] using wordTrace_append hprefix tailTrace_1247961
  have hstable : (prefixWord ++ tailWord_1247961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247961).length < 2 ^ (prefixWord ++ tailWord_1247961).sum := by decide
  have hdescent : baseEnd_1247961 < baseStart_1247961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247991 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 2, 6]
def baseStart_1247991 : Nat := 118140960795 + 1247991 * 2 ^ 59
def prefixEnd_1247991 : Nat := 4983230072969 + 3 ^ 40 * 1247991 * 2
def baseEnd_1247991 : Nat := 427212823656887975448733

theorem tailTrace_1247991 : CollatzResearch.WordTrace tailWord_1247991 prefixEnd_1247991 427212823656887975448733 := by
  unfold tailWord_1247991
  simp only [CollatzResearch.WordTrace]
  refine ⟨45517971221749221738975827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30345314147832814492650551 45517971221749221738975827)
  ·
    refine ⟨68276956832623832608463741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45517971221749221738975827 68276956832623832608463741)
    ·
      refine ⟨25603858812233937228173903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68276956832623832608463741 25603858812233937228173903)
      ·
        refine ⟨38405788218350905842260855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25603858812233937228173903 38405788218350905842260855)
        ·
          refine ⟨57608682327526358763391283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38405788218350905842260855 57608682327526358763391283)
          ·
            refine ⟨86413023491289538145086925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57608682327526358763391283 86413023491289538145086925)
            ·
              refine ⟨32404883809233576804407597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86413023491289538145086925 32404883809233576804407597)
              ·
                refine ⟨12151831428462591301652849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32404883809233576804407597 12151831428462591301652849)
                ·
                  refine ⟨9113873571346943476239637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12151831428462591301652849 9113873571346943476239637)
                  ·
                    refine ⟨427212823656887975448733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9113873571346943476239637 427212823656887975448733)
                    ·
                      rfl

theorem cell22_1247991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_1247991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1247991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1247991 prefixEnd_1247991 := by exact prefixLift 1247991
  have htrace : WordTrace (prefixWord ++ tailWord_1247991) baseStart_1247991 baseEnd_1247991 := by
    simpa [prefixWord, tailWord_1247991, baseEnd_1247991] using wordTrace_append hprefix tailTrace_1247991
  have hstable : (prefixWord ++ tailWord_1247991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247991).length < 2 ^ (prefixWord ++ tailWord_1247991).sum := by decide
  have hdescent : baseEnd_1247991 < baseStart_1247991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248040 : List Nat := [2, 1, 5, 1, 1, 1, 4, 2, 5]
def baseStart_1248040 : Nat := 118140960795 + 1248040 * 2 ^ 59
def prefixEnd_1248040 : Nat := 4983230072969 + 3 ^ 40 * 1248040 * 2
def baseEnd_1248040 : Nat := 142409865786089393657861

theorem tailTrace_1248040 : CollatzResearch.WordTrace tailWord_1248040 prefixEnd_1248040 142409865786089393657861 := by
  unfold tailWord_1248040
  simp only [CollatzResearch.WordTrace]
  refine ⟨22759879199285851553754787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30346505599047802071673049 22759879199285851553754787)
  ·
    refine ⟨34139818798928777330632181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22759879199285851553754787 34139818798928777330632181)
    ·
      refine ⟨3200608012399572874746767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34139818798928777330632181 3200608012399572874746767)
      ·
        refine ⟨4800912018599359312120151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3200608012399572874746767 4800912018599359312120151)
        ·
          refine ⟨7201368027899038968180227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4800912018599359312120151 7201368027899038968180227)
          ·
            refine ⟨10802052041848558452270341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7201368027899038968180227 10802052041848558452270341)
            ·
              refine ⟨2025384757846604709800689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10802052041848558452270341 2025384757846604709800689)
              ·
                refine ⟨1519038568384953532350517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2025384757846604709800689 1519038568384953532350517)
                ·
                  refine ⟨142409865786089393657861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1519038568384953532350517 142409865786089393657861)
                  ·
                    rfl

theorem cell22_1248040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 5].length) (baseStart_1248040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1248040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1248040 prefixEnd_1248040 := by exact prefixLift 1248040
  have htrace : WordTrace (prefixWord ++ tailWord_1248040) baseStart_1248040 baseEnd_1248040 := by
    simpa [prefixWord, tailWord_1248040, baseEnd_1248040] using wordTrace_append hprefix tailTrace_1248040
  have hstable : (prefixWord ++ tailWord_1248040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248040).length < 2 ^ (prefixWord ++ tailWord_1248040).sum := by decide
  have hdescent : baseEnd_1248040 < baseStart_1248040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248087 : List Nat := [1, 1, 3, 2, 4, 1, 4, 1, 1, 4]
def baseStart_1248087 : Nat := 118140960795 + 1248087 * 2 ^ 59
def prefixEnd_1248087 : Nat := 4983230072969 + 3 ^ 40 * 1248087 * 2
def baseEnd_1248087 : Nat := 427245686418775725048439

theorem tailTrace_1248087 : CollatzResearch.WordTrace tailWord_1248087 prefixEnd_1248087 427245686418775725048439 := by
  unfold tailWord_1248087
  simp only [CollatzResearch.WordTrace]
  refine ⟨45521472629401430134470515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30347648419600953422980343 45521472629401430134470515)
  ·
    refine ⟨68282208944102145201705773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45521472629401430134470515 68282208944102145201705773)
    ·
      refine ⟨25605828354038304450639665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68282208944102145201705773 25605828354038304450639665)
      ·
        refine ⟨19204371265528728337979749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25605828354038304450639665 19204371265528728337979749)
        ·
          refine ⟨3600819612286636563371203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19204371265528728337979749 3600819612286636563371203)
          ·
            refine ⟨5401229418429954845056805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3600819612286636563371203 5401229418429954845056805)
            ·
              refine ⟨1012730515955616533448151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5401229418429954845056805 1012730515955616533448151)
              ·
                refine ⟨1519095773933424800172227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1012730515955616533448151 1519095773933424800172227)
                ·
                  refine ⟨2278643660900137200258341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1519095773933424800172227 2278643660900137200258341)
                  ·
                    refine ⟨427245686418775725048439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2278643660900137200258341 427245686418775725048439)
                    ·
                      rfl

theorem cell22_1248087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 1, 4].length) (baseStart_1248087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1248087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1248087 prefixEnd_1248087 := by exact prefixLift 1248087
  have htrace : WordTrace (prefixWord ++ tailWord_1248087) baseStart_1248087 baseEnd_1248087 := by
    simpa [prefixWord, tailWord_1248087, baseEnd_1248087] using wordTrace_append hprefix tailTrace_1248087
  have hstable : (prefixWord ++ tailWord_1248087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248087).length < 2 ^ (prefixWord ++ tailWord_1248087).sum := by decide
  have hdescent : baseEnd_1248087 < baseStart_1248087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248117 : List Nat := [1, 3, 4, 1, 1, 4, 1, 1, 1, 5]
def baseStart_1248117 : Nat := 118140960795 + 1248117 * 2 ^ 59
def prefixEnd_1248117 : Nat := 4983230072969 + 3 ^ 40 * 1248117 * 2
def baseEnd_1248117 : Nat := 427255956031865646798347

theorem tailTrace_1248117 : CollatzResearch.WordTrace tailWord_1248117 prefixEnd_1248117 427255956031865646798347 := by
  unfold tailWord_1248117
  simp only [CollatzResearch.WordTrace]
  refine ⟨45522566819292745258062605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30348377879528496838708403 45522566819292745258062605)
  ·
    refine ⟨17070962557234779471773477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45522566819292745258062605 17070962557234779471773477)
    ·
      refine ⟨3200805479481521150957527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17070962557234779471773477 3200805479481521150957527)
      ·
        refine ⟨4801208219222281726436291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3200805479481521150957527 4801208219222281726436291)
        ·
          refine ⟨7201812328833422589654437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4801208219222281726436291 7201812328833422589654437)
          ·
            refine ⟨1350339811656266735560207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7201812328833422589654437 1350339811656266735560207)
            ·
              refine ⟨2025509717484400103340311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1350339811656266735560207 2025509717484400103340311)
              ·
                refine ⟨3038264576226600155010467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2025509717484400103340311 3038264576226600155010467)
                ·
                  refine ⟨4557396864339900232515701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3038264576226600155010467 4557396864339900232515701)
                  ·
                    refine ⟨427255956031865646798347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4557396864339900232515701 427255956031865646798347)
                    ·
                      rfl

theorem cell22_1248117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_1248117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1248117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1248117 prefixEnd_1248117 := by exact prefixLift 1248117
  have htrace : WordTrace (prefixWord ++ tailWord_1248117) baseStart_1248117 baseEnd_1248117 := by
    simpa [prefixWord, tailWord_1248117, baseEnd_1248117] using wordTrace_append hprefix tailTrace_1248117
  have hstable : (prefixWord ++ tailWord_1248117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248117).length < 2 ^ (prefixWord ++ tailWord_1248117).sum := by decide
  have hdescent : baseEnd_1248117 < baseStart_1248117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248213 : List Nat := [1, 3, 2, 3, 3, 2, 2, 2, 1, 3]
def baseStart_1248213 : Nat := 118140960795 + 1248213 * 2 ^ 59
def prefixEnd_1248213 : Nat := 4983230072969 + 3 ^ 40 * 1248213 * 2
def baseEnd_1248213 : Nat := 427288818793753396398053

theorem tailTrace_1248213 : CollatzResearch.WordTrace tailWord_1248213 prefixEnd_1248213 427288818793753396398053 := by
  unfold tailWord_1248213
  simp only [CollatzResearch.WordTrace]
  refine ⟨45526068226944953653557293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30350712151296635769038195 45526068226944953653557293)
  ·
    refine ⟨17072275585104357620083985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45526068226944953653557293 17072275585104357620083985)
    ·
      refine ⟨12804206688828268215062989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17072275585104357620083985 12804206688828268215062989)
      ·
        refine ⟨4801577508310600580648621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12804206688828268215062989 4801577508310600580648621)
        ·
          refine ⟨1800591565616475217743233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4801577508310600580648621 1800591565616475217743233)
          ·
            refine ⟨1350443674212356413307425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1800591565616475217743233 1350443674212356413307425)
            ·
              refine ⟨1012832755659267309980569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1350443674212356413307425 1012832755659267309980569)
              ·
                refine ⟨759624566744450482485427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1012832755659267309980569 759624566744450482485427)
                ·
                  refine ⟨1139436850116675723728141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 759624566744450482485427 1139436850116675723728141)
                  ·
                    refine ⟨427288818793753396398053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1139436850116675723728141 427288818793753396398053)
                    ·
                      rfl

theorem cell22_1248213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 2, 1, 3].length) (baseStart_1248213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1248213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1248213 prefixEnd_1248213 := by exact prefixLift 1248213
  have htrace : WordTrace (prefixWord ++ tailWord_1248213) baseStart_1248213 baseEnd_1248213 := by
    simpa [prefixWord, tailWord_1248213, baseEnd_1248213] using wordTrace_append hprefix tailTrace_1248213
  have hstable : (prefixWord ++ tailWord_1248213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248213).length < 2 ^ (prefixWord ++ tailWord_1248213).sum := by decide
  have hdescent : baseEnd_1248213 < baseStart_1248213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248235 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 8, 3]
def baseStart_1248235 : Nat := 118140960795 + 1248235 * 2 ^ 59
def prefixEnd_1248235 : Nat := 4983230072969 + 3 ^ 40 * 1248235 * 2
def baseEnd_1248235 : Nat := 427296349843352672347985

theorem tailTrace_1248235 : CollatzResearch.WordTrace tailWord_1248235 prefixEnd_1248235 427296349843352672347985 := by
  unfold tailWord_1248235
  simp only [CollatzResearch.WordTrace]
  refine ⟨45526870632865251410858159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30351247088576834273905439 45526870632865251410858159)
  ·
    refine ⟨68290305949297877116287239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45526870632865251410858159 68290305949297877116287239)
    ·
      refine ⟨102435458923946815674430859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68290305949297877116287239 102435458923946815674430859)
      ·
        refine ⟨153653188385920223511646289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102435458923946815674430859 153653188385920223511646289)
        ·
          refine ⟨115239891289440167633734717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153653188385920223511646289 115239891289440167633734717)
          ·
            refine ⟨43214959233540062862650519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115239891289440167633734717 43214959233540062862650519)
            ·
              refine ⟨64822438850310094293975779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43214959233540062862650519 64822438850310094293975779)
              ·
                refine ⟨97233658275465141440963669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64822438850310094293975779 97233658275465141440963669)
                ·
                  refine ⟨1139456932915607126261293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 97233658275465141440963669 1139456932915607126261293)
                  ·
                    refine ⟨427296349843352672347985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1139456932915607126261293 427296349843352672347985)
                    ·
                      rfl

theorem cell22_1248235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 8, 3].length) (baseStart_1248235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1248235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1248235 prefixEnd_1248235 := by exact prefixLift 1248235
  have htrace : WordTrace (prefixWord ++ tailWord_1248235) baseStart_1248235 baseEnd_1248235 := by
    simpa [prefixWord, tailWord_1248235, baseEnd_1248235] using wordTrace_append hprefix tailTrace_1248235
  have hstable : (prefixWord ++ tailWord_1248235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248235).length < 2 ^ (prefixWord ++ tailWord_1248235).sum := by decide
  have hdescent : baseEnd_1248235 < baseStart_1248235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248325 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 4, 5]
def baseStart_1248325 : Nat := 118140960795 + 1248325 * 2 ^ 59
def prefixEnd_1248325 : Nat := 4983230072969 + 3 ^ 40 * 1248325 * 2
def baseEnd_1248325 : Nat := 427327158682622437597709

theorem tailTrace_1248325 : CollatzResearch.WordTrace tailWord_1248325 prefixEnd_1248325 427327158682622437597709 := by
  unfold tailWord_1248325
  simp only [CollatzResearch.WordTrace]
  refine ⟨45530153202539196781634429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30353435468359464521089619 45530153202539196781634429)
  ·
    refine ⟨17073807450952198793112911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45530153202539196781634429 17073807450952198793112911)
    ·
      refine ⟨25610711176428298189669367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17073807450952198793112911 25610711176428298189669367)
      ·
        refine ⟨38416066764642447284504051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25610711176428298189669367 38416066764642447284504051)
        ·
          refine ⟨57624100146963670926756077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38416066764642447284504051 57624100146963670926756077)
          ·
            refine ⟨21609037555111376597533529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57624100146963670926756077 21609037555111376597533529)
            ·
              refine ⟨16206778166333532448150147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21609037555111376597533529 16206778166333532448150147)
              ·
                refine ⟨24310167249500298672225221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16206778166333532448150147 24310167249500298672225221)
                ·
                  refine ⟨4558156359281306001042229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24310167249500298672225221 4558156359281306001042229)
                  ·
                    refine ⟨427327158682622437597709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4558156359281306001042229 427327158682622437597709)
                    ·
                      rfl

theorem cell22_1248325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_1248325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1248325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1248325 prefixEnd_1248325 := by exact prefixLift 1248325
  have htrace : WordTrace (prefixWord ++ tailWord_1248325) baseStart_1248325 baseEnd_1248325 := by
    simpa [prefixWord, tailWord_1248325, baseEnd_1248325] using wordTrace_append hprefix tailTrace_1248325
  have hstable : (prefixWord ++ tailWord_1248325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248325).length < 2 ^ (prefixWord ++ tailWord_1248325).sum := by decide
  have hdescent : baseEnd_1248325 < baseStart_1248325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248355 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 8]
def baseStart_1248355 : Nat := 118140960795 + 1248355 * 2 ^ 59
def prefixEnd_1248355 : Nat := 4983230072969 + 3 ^ 40 * 1248355 * 2
def baseEnd_1248355 : Nat := 142445809431904119782539

theorem tailTrace_1248355 : CollatzResearch.WordTrace tailWord_1248355 prefixEnd_1248355 142445809431904119782539 := by
  unfold tailWord_1248355
  simp only [CollatzResearch.WordTrace]
  refine ⟨45531247392430511905226519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30354164928287007936817679 45531247392430511905226519)
  ·
    refine ⟨68296871088645767857839779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45531247392430511905226519 68296871088645767857839779)
    ·
      refine ⟨102445306632968651786759669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68296871088645767857839779 102445306632968651786759669)
      ·
        refine ⟨9604247496840811105008719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102445306632968651786759669 9604247496840811105008719)
        ·
          refine ⟨14406371245261216657513079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9604247496840811105008719 14406371245261216657513079)
          ·
            refine ⟨21609556867891824986269619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14406371245261216657513079 21609556867891824986269619)
            ·
              refine ⟨32414335301837737479404429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21609556867891824986269619 32414335301837737479404429)
              ·
                refine ⟨12155375738189151554776661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32414335301837737479404429 12155375738189151554776661)
                ·
                  refine ⟨142445809431904119782539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12155375738189151554776661 142445809431904119782539)
                  ·
                    rfl

theorem cell22_1248355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 8].length) (baseStart_1248355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1248355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1248355 prefixEnd_1248355 := by exact prefixLift 1248355
  have htrace : WordTrace (prefixWord ++ tailWord_1248355) baseStart_1248355 baseEnd_1248355 := by
    simpa [prefixWord, tailWord_1248355, baseEnd_1248355] using wordTrace_append hprefix tailTrace_1248355
  have hstable : (prefixWord ++ tailWord_1248355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248355).length < 2 ^ (prefixWord ++ tailWord_1248355).sum := by decide
  have hdescent : baseEnd_1248355 < baseStart_1248355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248357 : List Nat := [1, 3, 1, 3, 2, 1, 3, 1, 3, 4]
def baseStart_1248357 : Nat := 118140960795 + 1248357 * 2 ^ 59
def prefixEnd_1248357 : Nat := 4983230072969 + 3 ^ 40 * 1248357 * 2
def baseEnd_1248357 : Nat := 427338112936585020797611

theorem tailTrace_1248357 : CollatzResearch.WordTrace tailWord_1248357 prefixEnd_1248357 427338112936585020797611 := by
  unfold tailWord_1248357
  simp only [CollatzResearch.WordTrace]
  refine ⟨45531320338423266246799325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30354213558948844164532883 45531320338423266246799325)
  ·
    refine ⟨17074245126908724842549747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45531320338423266246799325 17074245126908724842549747)
    ·
      refine ⟨25611367690363087263824621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17074245126908724842549747 25611367690363087263824621)
      ·
        refine ⟨9604262883886157723934233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25611367690363087263824621 9604262883886157723934233)
        ·
          refine ⟨7203197162914618292950675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9604262883886157723934233 7203197162914618292950675)
          ·
            refine ⟨10804795744371927439426013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7203197162914618292950675 10804795744371927439426013)
            ·
              refine ⟨4051798404139472789784755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10804795744371927439426013 4051798404139472789784755)
              ·
                refine ⟨6077697606209209184677133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4051798404139472789784755 6077697606209209184677133)
                ·
                  refine ⟨2279136602328453444253925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6077697606209209184677133 2279136602328453444253925)
                  ·
                    refine ⟨427338112936585020797611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2279136602328453444253925 427338112936585020797611)
                    ·
                      rfl

theorem cell22_1248357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_1248357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1248357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1248357 prefixEnd_1248357 := by exact prefixLift 1248357
  have htrace : WordTrace (prefixWord ++ tailWord_1248357) baseStart_1248357 baseEnd_1248357 := by
    simpa [prefixWord, tailWord_1248357, baseEnd_1248357] using wordTrace_append hprefix tailTrace_1248357
  have hstable : (prefixWord ++ tailWord_1248357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248357).length < 2 ^ (prefixWord ++ tailWord_1248357).sum := by decide
  have hdescent : baseEnd_1248357 < baseStart_1248357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248382 : List Nat := [4, 2, 4, 1, 1, 1, 1, 4, 1, 3]
def baseStart_1248382 : Nat := 118140960795 + 1248382 * 2 ^ 59
def prefixEnd_1248382 : Nat := 4983230072969 + 3 ^ 40 * 1248382 * 2
def baseEnd_1248382 : Nat := 427346670947493288922535

theorem tailTrace_1248382 : CollatzResearch.WordTrace tailWord_1248382 prefixEnd_1248382 427346670947493288922535 := by
  unfold tailWord_1248382
  simp only [CollatzResearch.WordTrace]
  refine ⟨5691529020416586939557425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30354821442221797010972933 5691529020416586939557425)
  ·
    refine ⟨4268646765312440204668069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5691529020416586939557425 4268646765312440204668069)
    ·
      refine ⟨800371268496082538375263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4268646765312440204668069 800371268496082538375263)
      ·
        refine ⟨1200556902744123807562895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 800371268496082538375263 1200556902744123807562895)
        ·
          refine ⟨1800835354116185711344343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1200556902744123807562895 1800835354116185711344343)
          ·
            refine ⟨2701253031174278567016515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1800835354116185711344343 2701253031174278567016515)
            ·
              refine ⟨4051879546761417850524773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2701253031174278567016515 4051879546761417850524773)
              ·
                refine ⟨759727415017765846973395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4051879546761417850524773 759727415017765846973395)
                ·
                  refine ⟨1139591122526648770460093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 759727415017765846973395 1139591122526648770460093)
                  ·
                    refine ⟨427346670947493288922535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1139591122526648770460093 427346670947493288922535)
                    ·
                      rfl

theorem cell22_1248382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_1248382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1248382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1248382 prefixEnd_1248382 := by exact prefixLift 1248382
  have htrace : WordTrace (prefixWord ++ tailWord_1248382) baseStart_1248382 baseEnd_1248382 := by
    simpa [prefixWord, tailWord_1248382, baseEnd_1248382] using wordTrace_append hprefix tailTrace_1248382
  have hstable : (prefixWord ++ tailWord_1248382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248382).length < 2 ^ (prefixWord ++ tailWord_1248382).sum := by decide
  have hdescent : baseEnd_1248382 < baseStart_1248382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248400 : List Nat := [2, 1, 1, 1, 1, 1, 4, 11]
def baseStart_1248400 : Nat := 118140960795 + 1248400 * 2 ^ 59
def prefixEnd_1248400 : Nat := 4983230072969 + 3 ^ 40 * 1248400 * 2
def baseEnd_1248400 : Nat := 47483648079483026885831

theorem tailTrace_1248400 : CollatzResearch.WordTrace tailWord_1248400 prefixEnd_1248400 47483648079483026885831 := by
  unfold tailWord_1248400
  simp only [CollatzResearch.WordTrace]
  refine ⟨22766444338633742295307327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30355259118178323060409769 22766444338633742295307327)
  ·
    refine ⟨34149666507950613442960991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22766444338633742295307327 34149666507950613442960991)
    ·
      refine ⟨51224499761925920164441487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34149666507950613442960991 51224499761925920164441487)
      ·
        refine ⟨76836749642888880246662231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51224499761925920164441487 76836749642888880246662231)
        ·
          refine ⟨115255124464333320369993347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76836749642888880246662231 115255124464333320369993347)
          ·
            refine ⟨172882686696499980554990021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115255124464333320369993347 172882686696499980554990021)
            ·
              refine ⟨32415503755593746354060629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 172882686696499980554990021 32415503755593746354060629)
              ·
                refine ⟨47483648079483026885831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 32415503755593746354060629 47483648079483026885831)
                ·
                  rfl

theorem cell22_1248400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 11].length) (baseStart_1248400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1248400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1248400 prefixEnd_1248400 := by exact prefixLift 1248400
  have htrace : WordTrace (prefixWord ++ tailWord_1248400) baseStart_1248400 baseEnd_1248400 := by
    simpa [prefixWord, tailWord_1248400, baseEnd_1248400] using wordTrace_append hprefix tailTrace_1248400
  have hstable : (prefixWord ++ tailWord_1248400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248400).length < 2 ^ (prefixWord ++ tailWord_1248400).sum := by decide
  have hdescent : baseEnd_1248400 < baseStart_1248400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248468 : List Nat := [2, 4, 1, 4, 1, 2, 2, 6]
def baseStart_1248468 : Nat := 118140960795 + 1248468 * 2 ^ 59
def prefixEnd_1248468 : Nat := 4983230072969 + 3 ^ 40 * 1248468 * 2
def baseEnd_1248468 : Nat := 47486234500557525696919

theorem tailTrace_1248468 : CollatzResearch.WordTrace tailWord_1248468 prefixEnd_1248468 47486234500557525696919 := by
  unfold tailWord_1248468
  simp only [CollatzResearch.WordTrace]
  refine ⟨22767684420510566102045029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30356912560680754802726705 22767684420510566102045029)
  ·
    refine ⟨4268940828845731144133443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22767684420510566102045029 4268940828845731144133443)
    ·
      refine ⟨6403411243268596716200165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4268940828845731144133443 6403411243268596716200165)
      ·
        refine ⟨1200639608112861884287531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6403411243268596716200165 1200639608112861884287531)
        ·
          refine ⟨1800959412169292826431297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1200639608112861884287531 1800959412169292826431297)
          ·
            refine ⟨1350719559126969619823473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1800959412169292826431297 1350719559126969619823473)
            ·
              refine ⟨1013039669345227214867605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1350719559126969619823473 1013039669345227214867605)
              ·
                refine ⟨47486234500557525696919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1013039669345227214867605 47486234500557525696919)
                ·
                  rfl

theorem cell22_1248468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 6].length) (baseStart_1248468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1248468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1248468 prefixEnd_1248468 := by exact prefixLift 1248468
  have htrace : WordTrace (prefixWord ++ tailWord_1248468) baseStart_1248468 baseEnd_1248468 := by
    simpa [prefixWord, tailWord_1248468, baseEnd_1248468] using wordTrace_append hprefix tailTrace_1248468
  have hstable : (prefixWord ++ tailWord_1248468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248468).length < 2 ^ (prefixWord ++ tailWord_1248468).sum := by decide
  have hdescent : baseEnd_1248468 < baseStart_1248468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248526 : List Nat := [4, 1, 1, 2, 1, 3, 3, 2, 1, 4]
def baseStart_1248526 : Nat := 118140960795 + 1248526 * 2 ^ 59
def prefixEnd_1248526 : Nat := 4983230072969 + 3 ^ 40 * 1248526 * 2
def baseEnd_1248526 : Nat := 427395965090324913322093

theorem tailTrace_1248526 : CollatzResearch.WordTrace tailWord_1248526 prefixEnd_1248526 427395965090324913322093 := by
  unfold tailWord_1248526
  simp only [CollatzResearch.WordTrace]
  refine ⟨5692185534351376013712679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30358322849874005406467621 5692185534351376013712679)
  ·
    refine ⟨8538278301527064020569019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5692185534351376013712679 8538278301527064020569019)
    ·
      refine ⟨12807417452290596030853529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8538278301527064020569019 12807417452290596030853529)
      ·
        refine ⟨9605563089217947023140147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12807417452290596030853529 9605563089217947023140147)
        ·
          refine ⟨14408344633826920534710221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9605563089217947023140147 14408344633826920534710221)
          ·
            refine ⟨5403129237685095200516333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14408344633826920534710221 5403129237685095200516333)
            ·
              refine ⟨2026173464131910700193625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5403129237685095200516333 2026173464131910700193625)
              ·
                refine ⟨1519630098098933025145219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2026173464131910700193625 1519630098098933025145219)
                ·
                  refine ⟨2279445147148399537717829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1519630098098933025145219 2279445147148399537717829)
                  ·
                    refine ⟨427395965090324913322093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2279445147148399537717829 427395965090324913322093)
                    ·
                      rfl

theorem cell22_1248526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_1248526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1248526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1248526 prefixEnd_1248526 := by exact prefixLift 1248526
  have htrace : WordTrace (prefixWord ++ tailWord_1248526) baseStart_1248526 baseEnd_1248526 := by
    simpa [prefixWord, tailWord_1248526, baseEnd_1248526] using wordTrace_append hprefix tailTrace_1248526
  have hstable : (prefixWord ++ tailWord_1248526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248526).length < 2 ^ (prefixWord ++ tailWord_1248526).sum := by decide
  have hdescent : baseEnd_1248526 < baseStart_1248526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248543 : List Nat := [1, 1, 2, 4, 4, 1, 3, 1, 1, 4]
def baseStart_1248543 : Nat := 118140960795 + 1248543 * 2 ^ 59
def prefixEnd_1248543 : Nat := 4983230072969 + 3 ^ 40 * 1248543 * 2
def baseEnd_1248543 : Nat := 427401784537742535647041

theorem tailTrace_1248543 : CollatzResearch.WordTrace tailWord_1248543 prefixEnd_1248543 427401784537742535647041 := by
  unfold tailWord_1248543
  simp only [CollatzResearch.WordTrace]
  refine ⟨45538104315749420013070283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30358736210499613342046855 45538104315749420013070283)
  ·
    refine ⟨68307156473624130019605425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45538104315749420013070283 68307156473624130019605425)
    ·
      refine ⟨51230367355218097514704069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68307156473624130019605425 51230367355218097514704069)
      ·
        refine ⟨9605693879103393284007013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51230367355218097514704069 9605693879103393284007013)
        ·
          refine ⟨1801067602331886240751315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9605693879103393284007013 1801067602331886240751315)
          ·
            refine ⟨2701601403497829361126973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1801067602331886240751315 2701601403497829361126973)
            ·
              refine ⟨1013100526311686010422615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2701601403497829361126973 1013100526311686010422615)
              ·
                refine ⟨1519650789467529015633923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1013100526311686010422615 1519650789467529015633923)
                ·
                  refine ⟨2279476184201293523450885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1519650789467529015633923 2279476184201293523450885)
                  ·
                    refine ⟨427401784537742535647041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2279476184201293523450885 427401784537742535647041)
                    ·
                      rfl

theorem cell22_1248543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 1, 4].length) (baseStart_1248543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1248543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1248543 prefixEnd_1248543 := by exact prefixLift 1248543
  have htrace : WordTrace (prefixWord ++ tailWord_1248543) baseStart_1248543 baseEnd_1248543 := by
    simpa [prefixWord, tailWord_1248543, baseEnd_1248543] using wordTrace_append hprefix tailTrace_1248543
  have hstable : (prefixWord ++ tailWord_1248543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248543).length < 2 ^ (prefixWord ++ tailWord_1248543).sum := by decide
  have hdescent : baseEnd_1248543 < baseStart_1248543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248567 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 4, 7]
def baseStart_1248567 : Nat := 118140960795 + 1248567 * 2 ^ 59
def prefixEnd_1248567 : Nat := 4983230072969 + 3 ^ 40 * 1248567 * 2
def baseEnd_1248567 : Nat := 427410000228214473046967

theorem tailTrace_1248567 : CollatzResearch.WordTrace tailWord_1248567 prefixEnd_1248567 427410000228214473046967 := by
  unfold tailWord_1248567
  simp only [CollatzResearch.WordTrace]
  refine ⟨45538979667662472111943955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30359319778441648074629303 45538979667662472111943955)
  ·
    refine ⟨68308469501493708167915933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45538979667662472111943955 68308469501493708167915933)
    ·
      refine ⟨25615676063060140562968475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68308469501493708167915933 25615676063060140562968475)
      ·
        refine ⟨38423514094590210844452713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25615676063060140562968475 38423514094590210844452713)
        ·
          refine ⟨28817635570942658133339535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38423514094590210844452713 28817635570942658133339535)
          ·
            refine ⟨43226453356413987200009303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28817635570942658133339535 43226453356413987200009303)
            ·
              refine ⟨64839680034620980800013955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43226453356413987200009303 64839680034620980800013955)
              ·
                refine ⟨97259520051931471200020933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64839680034620980800013955 97259520051931471200020933)
                ·
                  refine ⟨18236160009737150850003925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97259520051931471200020933 18236160009737150850003925)
                  ·
                    refine ⟨427410000228214473046967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18236160009737150850003925 427410000228214473046967)
                    ·
                      rfl

theorem cell22_1248567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_1248567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1248567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1248567 prefixEnd_1248567 := by exact prefixLift 1248567
  have htrace : WordTrace (prefixWord ++ tailWord_1248567) baseStart_1248567 baseEnd_1248567 := by
    simpa [prefixWord, tailWord_1248567, baseEnd_1248567] using wordTrace_append hprefix tailTrace_1248567
  have hstable : (prefixWord ++ tailWord_1248567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248567).length < 2 ^ (prefixWord ++ tailWord_1248567).sum := by decide
  have hdescent : baseEnd_1248567 < baseStart_1248567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248573 : List Nat := [1, 4, 1, 5, 1, 1, 2, 1, 1, 5]
def baseStart_1248573 : Nat := 118140960795 + 1248573 * 2 ^ 59
def prefixEnd_1248573 : Nat := 4983230072969 + 3 ^ 40 * 1248573 * 2
def baseEnd_1248573 : Nat := 427412054150832457396949

theorem tailTrace_1248573 : CollatzResearch.WordTrace tailWord_1248573 prefixEnd_1248573 427412054150832457396949 := by
  unfold tailWord_1248573
  simp only [CollatzResearch.WordTrace]
  refine ⟨45539198505640735136662373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30359465670427156757774915 45539198505640735136662373)
  ·
    refine ⟨8538599719807637838124195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45539198505640735136662373 8538599719807637838124195)
    ·
      refine ⟨12807899579711456757186293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8538599719807637838124195 12807899579711456757186293)
      ·
        refine ⟨1200740585597949070986215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12807899579711456757186293 1200740585597949070986215)
        ·
          refine ⟨1801110878396923606479323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1200740585597949070986215 1801110878396923606479323)
          ·
            refine ⟨2701666317595385409718985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1801110878396923606479323 2701666317595385409718985)
            ·
              refine ⟨2026249738196539057289239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2701666317595385409718985 2026249738196539057289239)
              ·
                refine ⟨3039374607294808585933859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2026249738196539057289239 3039374607294808585933859)
                ·
                  refine ⟨4559061910942212878900789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3039374607294808585933859 4559061910942212878900789)
                  ·
                    refine ⟨427412054150832457396949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4559061910942212878900789 427412054150832457396949)
                    ·
                      rfl

theorem cell22_1248573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_1248573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1248573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1248573 prefixEnd_1248573 := by exact prefixLift 1248573
  have htrace : WordTrace (prefixWord ++ tailWord_1248573) baseStart_1248573 baseEnd_1248573 := by
    simpa [prefixWord, tailWord_1248573, baseEnd_1248573] using wordTrace_append hprefix tailTrace_1248573
  have hstable : (prefixWord ++ tailWord_1248573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248573).length < 2 ^ (prefixWord ++ tailWord_1248573).sum := by decide
  have hdescent : baseEnd_1248573 < baseStart_1248573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248631 : List Nat := [1, 1, 3, 1, 1, 2, 7, 1, 5]
def baseStart_1248631 : Nat := 118140960795 + 1248631 * 2 ^ 59
def prefixEnd_1248631 : Nat := 4983230072969 + 3 ^ 40 * 1248631 * 2
def baseEnd_1248631 : Nat := 142477302912046546482257

theorem tailTrace_1248631 : CollatzResearch.WordTrace tailWord_1248631 prefixEnd_1248631 142477302912046546482257 := by
  unfold tailWord_1248631
  simp only [CollatzResearch.WordTrace]
  refine ⟨45541313939430611042273747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30360875959620407361515831 45541313939430611042273747)
  ·
    refine ⟨68311970909145916563410621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45541313939430611042273747 68311970909145916563410621)
    ·
      refine ⟨25616989090929718711278983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68311970909145916563410621 25616989090929718711278983)
      ·
        refine ⟨38425483636394578066918475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25616989090929718711278983 38425483636394578066918475)
        ·
          refine ⟨57638225454591867100377713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38425483636394578066918475 57638225454591867100377713)
          ·
            refine ⟨43228669090943900325283285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57638225454591867100377713 43228669090943900325283285)
            ·
              refine ⟨1013171931818997663873827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 43228669090943900325283285 1013171931818997663873827)
              ·
                refine ⟨1519757897728496495810741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1013171931818997663873827 1519757897728496495810741)
                ·
                  refine ⟨142477302912046546482257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1519757897728496495810741 142477302912046546482257)
                  ·
                    rfl

theorem cell22_1248631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 5].length) (baseStart_1248631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1248631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1248631 prefixEnd_1248631 := by exact prefixLift 1248631
  have htrace : WordTrace (prefixWord ++ tailWord_1248631) baseStart_1248631 baseEnd_1248631 := by
    simpa [prefixWord, tailWord_1248631, baseEnd_1248631] using wordTrace_append hprefix tailTrace_1248631
  have hstable : (prefixWord ++ tailWord_1248631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248631).length < 2 ^ (prefixWord ++ tailWord_1248631).sum := by decide
  have hdescent : baseEnd_1248631 < baseStart_1248631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248661 : List Nat := [1, 3, 2, 1, 1, 2, 4, 3, 1, 4]
def baseStart_1248661 : Nat := 118140960795 + 1248661 * 2 ^ 59
def prefixEnd_1248661 : Nat := 4983230072969 + 3 ^ 40 * 1248661 * 2
def baseEnd_1248661 : Nat := 427442178349229561196679

theorem tailTrace_1248661 : CollatzResearch.WordTrace tailWord_1248661 prefixEnd_1248661 427442178349229561196679 := by
  unfold tailWord_1248661
  simp only [CollatzResearch.WordTrace]
  refine ⟨45542408129321926165865837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30361605419547950777243891 45542408129321926165865837)
  ·
    refine ⟨17078403048495722312199689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45542408129321926165865837 17078403048495722312199689)
    ·
      refine ⟨12808802286371791734149767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17078403048495722312199689 12808802286371791734149767)
      ·
        refine ⟨19213203429557687601224651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12808802286371791734149767 19213203429557687601224651)
        ·
          refine ⟨28819805144336531401836977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19213203429557687601224651 28819805144336531401836977)
          ·
            refine ⟨21614853858252398551377733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28819805144336531401836977 21614853858252398551377733)
            ·
              refine ⟨4052785098422324728383325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21614853858252398551377733 4052785098422324728383325)
              ·
                refine ⟨1519794411908371773143747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4052785098422324728383325 1519794411908371773143747)
                ·
                  refine ⟨2279691617862557659715621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1519794411908371773143747 2279691617862557659715621)
                  ·
                    refine ⟨427442178349229561196679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2279691617862557659715621 427442178349229561196679)
                    ·
                      rfl

theorem cell22_1248661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_1248661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1248661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1248661 prefixEnd_1248661 := by exact prefixLift 1248661
  have htrace : WordTrace (prefixWord ++ tailWord_1248661) baseStart_1248661 baseEnd_1248661 := by
    simpa [prefixWord, tailWord_1248661, baseEnd_1248661] using wordTrace_append hprefix tailTrace_1248661
  have hstable : (prefixWord ++ tailWord_1248661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248661).length < 2 ^ (prefixWord ++ tailWord_1248661).sum := by decide
  have hdescent : baseEnd_1248661 < baseStart_1248661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248704 : List Nat := [2, 1, 1, 2, 3, 1, 4, 8]
def baseStart_1248704 : Nat := 118140960795 + 1248704 * 2 ^ 59
def prefixEnd_1248704 : Nat := 4983230072969 + 3 ^ 40 * 1248704 * 2
def baseEnd_1248704 : Nat := 47495210903110198041283

theorem tailTrace_1248704 : CollatzResearch.WordTrace tailWord_1248704 prefixEnd_1248704 47495210903110198041283 := by
  unfold tailWord_1248704
  simp only [CollatzResearch.WordTrace]
  refine ⟨22771988234083072254840583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30362650978777429673120777 22771988234083072254840583)
  ·
    refine ⟨34157982351124608382260875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22771988234083072254840583 34157982351124608382260875)
    ·
      refine ⟨51236973526686912573391313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34157982351124608382260875 51236973526686912573391313)
      ·
        refine ⟨38427730145015184430043485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51236973526686912573391313 38427730145015184430043485)
        ·
          refine ⟨14410398804380694161266307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38427730145015184430043485 14410398804380694161266307)
          ·
            refine ⟨21615598206571041241899461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14410398804380694161266307 21615598206571041241899461)
            ·
              refine ⟨4052924663732070232856149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21615598206571041241899461 4052924663732070232856149)
              ·
                refine ⟨47495210903110198041283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4052924663732070232856149 47495210903110198041283)
                ·
                  rfl

theorem cell22_1248704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 8].length) (baseStart_1248704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1248704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1248704 prefixEnd_1248704 := by exact prefixLift 1248704
  have htrace : WordTrace (prefixWord ++ tailWord_1248704) baseStart_1248704 baseEnd_1248704 := by
    simpa [prefixWord, tailWord_1248704, baseEnd_1248704] using wordTrace_append hprefix tailTrace_1248704
  have hstable : (prefixWord ++ tailWord_1248704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248704).length < 2 ^ (prefixWord ++ tailWord_1248704).sum := by decide
  have hdescent : baseEnd_1248704 < baseStart_1248704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248708 : List Nat := [2, 3, 3, 2, 1, 2, 1, 2, 1, 5]
def baseStart_1248708 : Nat := 118140960795 + 1248708 * 2 ^ 59
def prefixEnd_1248708 : Nat := 4983230072969 + 3 ^ 40 * 1248708 * 2
def baseEnd_1248708 : Nat := 427458267409737105271535

theorem tailTrace_1248708 : CollatzResearch.WordTrace tailWord_1248708 prefixEnd_1248708 427458267409737105271535 := by
  unfold tailWord_1248708
  simp only [CollatzResearch.WordTrace]
  refine ⟨22772061180075826596413389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30362748240101102128551185 22772061180075826596413389)
  ·
    refine ⟨8539522942528434973655021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22772061180075826596413389 8539522942528434973655021)
    ·
      refine ⟨3202321103448163115120633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8539522942528434973655021 3202321103448163115120633)
      ·
        refine ⟨2401740827586122336340475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3202321103448163115120633 2401740827586122336340475)
        ·
          refine ⟨3602611241379183504510713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2401740827586122336340475 3602611241379183504510713)
          ·
            refine ⟨2701958431034387628383035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3602611241379183504510713 2701958431034387628383035)
            ·
              refine ⟨4052937646551581442574553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2701958431034387628383035 4052937646551581442574553)
              ·
                refine ⟨3039703234913686081930915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4052937646551581442574553 3039703234913686081930915)
                ·
                  refine ⟨4559554852370529122896373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3039703234913686081930915 4559554852370529122896373)
                  ·
                    refine ⟨427458267409737105271535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4559554852370529122896373 427458267409737105271535)
                    ·
                      rfl

theorem cell22_1248708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_1248708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1248708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1248708 prefixEnd_1248708 := by exact prefixLift 1248708
  have htrace : WordTrace (prefixWord ++ tailWord_1248708) baseStart_1248708 baseEnd_1248708 := by
    simpa [prefixWord, tailWord_1248708, baseEnd_1248708] using wordTrace_append hprefix tailTrace_1248708
  have hstable : (prefixWord ++ tailWord_1248708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248708).length < 2 ^ (prefixWord ++ tailWord_1248708).sum := by decide
  have hdescent : baseEnd_1248708 < baseStart_1248708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248753 : List Nat := [1, 2, 2, 2, 3, 3, 1, 2, 3, 3]
def baseStart_1248753 : Nat := 118140960795 + 1248753 * 2 ^ 59
def prefixEnd_1248753 : Nat := 4983230072969 + 3 ^ 40 * 1248753 * 2
def baseEnd_1248753 : Nat := 427473671829371987896397

theorem tailTrace_1248753 : CollatzResearch.WordTrace tailWord_1248753 prefixEnd_1248753 427473671829371987896397 := by
  unfold tailWord_1248753
  simp only [CollatzResearch.WordTrace]
  refine ⟨45545763644988625878214913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30363842429992417252143275 45545763644988625878214913)
  ·
    refine ⟨34159322733741469408661185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45545763644988625878214913 34159322733741469408661185)
    ·
      refine ⟨25619492050306102056495889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34159322733741469408661185 25619492050306102056495889)
      ·
        refine ⟨19214619037729576542371917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25619492050306102056495889 19214619037729576542371917)
        ·
          refine ⟨7205482139148591203389469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19214619037729576542371917 7205482139148591203389469)
          ·
            refine ⟨2702055802180721701271051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7205482139148591203389469 2702055802180721701271051)
            ·
              refine ⟨4053083703271082551906577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2702055802180721701271051 4053083703271082551906577)
              ·
                refine ⟨3039812777453311913929933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4053083703271082551906577 3039812777453311913929933)
                ·
                  refine ⟨1139929791544991967723725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3039812777453311913929933 1139929791544991967723725)
                  ·
                    refine ⟨427473671829371987896397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1139929791544991967723725 427473671829371987896397)
                    ·
                      rfl

theorem cell22_1248753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 2, 3, 3].length) (baseStart_1248753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1248753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1248753 prefixEnd_1248753 := by exact prefixLift 1248753
  have htrace : WordTrace (prefixWord ++ tailWord_1248753) baseStart_1248753 baseEnd_1248753 := by
    simpa [prefixWord, tailWord_1248753, baseEnd_1248753] using wordTrace_append hprefix tailTrace_1248753
  have hstable : (prefixWord ++ tailWord_1248753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248753).length < 2 ^ (prefixWord ++ tailWord_1248753).sum := by decide
  have hdescent : baseEnd_1248753 < baseStart_1248753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248800 : List Nat := [2, 1, 1, 6, 1, 2, 3, 1, 5]
def baseStart_1248800 : Nat := 118140960795 + 1248800 * 2 ^ 59
def prefixEnd_1248800 : Nat := 4983230072969 + 3 ^ 40 * 1248800 * 2
def baseEnd_1248800 : Nat := 142496586963293177323751

theorem tailTrace_1248800 : CollatzResearch.WordTrace tailWord_1248800 prefixEnd_1248800 142496586963293177323751 := by
  unfold tailWord_1248800
  simp only [CollatzResearch.WordTrace]
  refine ⟨22773738937909176452587927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30364985250545568603450569 22773738937909176452587927)
  ·
    refine ⟨34160608406863764678881891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22773738937909176452587927 34160608406863764678881891)
    ·
      refine ⟨51240912610295647018322837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34160608406863764678881891 51240912610295647018322837)
      ·
        refine ⟨2401917778607608453983883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 51240912610295647018322837 2401917778607608453983883)
        ·
          refine ⟨3602876667911412680975825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2401917778607608453983883 3602876667911412680975825)
          ·
            refine ⟨2702157500933559510731869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3602876667911412680975825 2702157500933559510731869)
            ·
              refine ⟨1013309062850084816524451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2702157500933559510731869 1013309062850084816524451)
              ·
                refine ⟨1519963594275127224786677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1013309062850084816524451 1519963594275127224786677)
                ·
                  refine ⟨142496586963293177323751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1519963594275127224786677 142496586963293177323751)
                  ·
                    rfl

theorem cell22_1248800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 5].length) (baseStart_1248800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1248800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1248800 prefixEnd_1248800 := by exact prefixLift 1248800
  have htrace : WordTrace (prefixWord ++ tailWord_1248800) baseStart_1248800 baseEnd_1248800 := by
    simpa [prefixWord, tailWord_1248800, baseEnd_1248800] using wordTrace_append hprefix tailTrace_1248800
  have hstable : (prefixWord ++ tailWord_1248800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248800).length < 2 ^ (prefixWord ++ tailWord_1248800).sum := by decide
  have hdescent : baseEnd_1248800 < baseStart_1248800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248826 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 3, 5]
def baseStart_1248826 : Nat := 118140960795 + 1248826 * 2 ^ 59
def prefixEnd_1248826 : Nat := 4983230072969 + 3 ^ 40 * 1248826 * 2
def baseEnd_1248826 : Nat := 427498661221224130821173

theorem tailTrace_1248826 : CollatzResearch.WordTrace tailWord_1248826 prefixEnd_1248826 427498661221224130821173 := by
  unfold tailWord_1248826
  simp only [CollatzResearch.WordTrace]
  refine ⟨11387106543431039836405583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30365617449149439563748221 11387106543431039836405583)
  ·
    refine ⟨17080659815146559754608375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11387106543431039836405583 17080659815146559754608375)
    ·
      refine ⟨25620989722719839631912563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17080659815146559754608375 25620989722719839631912563)
      ·
        refine ⟨38431484584079759447868845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25620989722719839631912563 38431484584079759447868845)
        ·
          refine ⟨14411806719029909792950817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38431484584079759447868845 14411806719029909792950817)
          ·
            refine ⟨10808855039272432344713113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14411806719029909792950817 10808855039272432344713113)
            ·
              refine ⟨8106641279454324258534835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10808855039272432344713113 8106641279454324258534835)
              ·
                refine ⟨12159961919181486387802253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8106641279454324258534835 12159961919181486387802253)
                ·
                  refine ⟨4559985719693057395425845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12159961919181486387802253 4559985719693057395425845)
                  ·
                    refine ⟨427498661221224130821173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4559985719693057395425845 427498661221224130821173)
                    ·
                      rfl

theorem cell22_1248826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_1248826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1248826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1248826 prefixEnd_1248826 := by exact prefixLift 1248826
  have htrace : WordTrace (prefixWord ++ tailWord_1248826) baseStart_1248826 baseEnd_1248826 := by
    simpa [prefixWord, tailWord_1248826, baseEnd_1248826] using wordTrace_append hprefix tailTrace_1248826
  have hstable : (prefixWord ++ tailWord_1248826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248826).length < 2 ^ (prefixWord ++ tailWord_1248826).sum := by decide
  have hdescent : baseEnd_1248826 < baseStart_1248826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248843 : List Nat := [1, 1, 1, 1, 3, 1, 3, 6, 2, 3]
def baseStart_1248843 : Nat := 118140960795 + 1248843 * 2 ^ 59
def prefixEnd_1248843 : Nat := 4983230072969 + 3 ^ 40 * 1248843 * 2
def baseEnd_1248843 : Nat := 427504480668641753146121

theorem tailTrace_1248843 : CollatzResearch.WordTrace tailWord_1248843 prefixEnd_1248843 427504480668641753146121 := by
  unfold tailWord_1248843
  simp only [CollatzResearch.WordTrace]
  refine ⟨45549046214662571248991183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30366030809775047499327455 45549046214662571248991183)
  ·
    refine ⟨68323569321993856873486775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45549046214662571248991183 68323569321993856873486775)
    ·
      refine ⟨102485353982990785310230163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68323569321993856873486775 102485353982990785310230163)
      ·
        refine ⟨153728030974486177965345245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102485353982990785310230163 153728030974486177965345245)
        ·
          refine ⟨57648011615432316737004467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153728030974486177965345245 57648011615432316737004467)
          ·
            refine ⟨86472017423148475105506701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57648011615432316737004467 86472017423148475105506701)
            ·
              refine ⟨32427006533680678164565013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86472017423148475105506701 32427006533680678164565013)
              ·
                refine ⟨1520015931266281788963985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32427006533680678164565013 1520015931266281788963985)
                ·
                  refine ⟨1140011948449711341722989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1520015931266281788963985 1140011948449711341722989)
                  ·
                    refine ⟨427504480668641753146121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1140011948449711341722989 427504480668641753146121)
                    ·
                      rfl

theorem cell22_1248843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 2, 3].length) (baseStart_1248843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1248843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1248843 prefixEnd_1248843 := by exact prefixLift 1248843
  have htrace : WordTrace (prefixWord ++ tailWord_1248843) baseStart_1248843 baseEnd_1248843 := by
    simpa [prefixWord, tailWord_1248843, baseEnd_1248843] using wordTrace_append hprefix tailTrace_1248843
  have hstable : (prefixWord ++ tailWord_1248843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248843).length < 2 ^ (prefixWord ++ tailWord_1248843).sum := by decide
  have hdescent : baseEnd_1248843 < baseStart_1248843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248871 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 2, 7]
def baseStart_1248871 : Nat := 118140960795 + 1248871 * 2 ^ 59
def prefixEnd_1248871 : Nat := 4983230072969 + 3 ^ 40 * 1248871 * 2
def baseEnd_1248871 : Nat := 427514065640859013446035

theorem tailTrace_1248871 : CollatzResearch.WordTrace tailWord_1248871 prefixEnd_1248871 427514065640859013446035 := by
  unfold tailWord_1248871
  simp only [CollatzResearch.WordTrace]
  refine ⟨45550067458561132031010467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30366711639040754687340311 45550067458561132031010467)
  ·
    refine ⟨68325101187841698046515701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45550067458561132031010467 68325101187841698046515701)
    ·
      refine ⟨6405478236360159191860847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68325101187841698046515701 6405478236360159191860847)
      ·
        refine ⟨9608217354540238787791271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6405478236360159191860847 9608217354540238787791271)
        ·
          refine ⟨14412326031810358181686907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9608217354540238787791271 14412326031810358181686907)
          ·
            refine ⟨21618489047715537272530361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14412326031810358181686907 21618489047715537272530361)
            ·
              refine ⟨16213866785786652954397771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21618489047715537272530361 16213866785786652954397771)
              ·
                refine ⟨24320800178679979431596657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16213866785786652954397771 24320800178679979431596657)
                ·
                  refine ⟨18240600134009984573697493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24320800178679979431596657 18240600134009984573697493)
                  ·
                    refine ⟨427514065640859013446035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18240600134009984573697493 427514065640859013446035)
                    ·
                      rfl

theorem cell22_1248871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_1248871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1248871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1248871 prefixEnd_1248871 := by exact prefixLift 1248871
  have htrace : WordTrace (prefixWord ++ tailWord_1248871) baseStart_1248871 baseEnd_1248871 := by
    simpa [prefixWord, tailWord_1248871, baseEnd_1248871] using wordTrace_append hprefix tailTrace_1248871
  have hstable : (prefixWord ++ tailWord_1248871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248871).length < 2 ^ (prefixWord ++ tailWord_1248871).sum := by decide
  have hdescent : baseEnd_1248871 < baseStart_1248871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248980 : List Nat := [2, 4, 1, 3, 1, 1, 2, 2, 6]
def baseStart_1248980 : Nat := 118140960795 + 1248980 * 2 ^ 59
def prefixEnd_1248980 : Nat := 4983230072969 + 3 ^ 40 * 1248980 * 2
def baseEnd_1248980 : Nat := 142517126189473020823567

theorem tailTrace_1248980 : CollatzResearch.WordTrace tailWord_1248980 prefixEnd_1248980 142517126189473020823567 := by
  unfold tailWord_1248980
  simp only [CollatzResearch.WordTrace]
  refine ⟨22777021507583121823364197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30369362010110829097818929 22777021507583121823364197)
  ·
    refine ⟨4270691532671835341880787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22777021507583121823364197 4270691532671835341880787)
    ·
      refine ⟨6406037299007753012821181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4270691532671835341880787 6406037299007753012821181)
      ·
        refine ⟨2402263987127907379807943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6406037299007753012821181 2402263987127907379807943)
        ·
          refine ⟨3603395980691861069711915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2402263987127907379807943 3603395980691861069711915)
          ·
            refine ⟨5405093971037791604567873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3603395980691861069711915 5405093971037791604567873)
            ·
              refine ⟨4053820478278343703425905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5405093971037791604567873 4053820478278343703425905)
              ·
                refine ⟨3040365358708757777569429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4053820478278343703425905 3040365358708757777569429)
                ·
                  refine ⟨142517126189473020823567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3040365358708757777569429 142517126189473020823567)
                  ·
                    rfl

theorem cell22_1248980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_1248980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1248980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1248980 prefixEnd_1248980 := by exact prefixLift 1248980
  have htrace : WordTrace (prefixWord ++ tailWord_1248980) baseStart_1248980 baseEnd_1248980 := by
    simpa [prefixWord, tailWord_1248980, baseEnd_1248980] using wordTrace_append hprefix tailTrace_1248980
  have hstable : (prefixWord ++ tailWord_1248980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248980).length < 2 ^ (prefixWord ++ tailWord_1248980).sum := by decide
  have hdescent : baseEnd_1248980 < baseStart_1248980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249010 : List Nat := [3, 2, 1, 3, 1, 1, 3, 2, 2, 4]
def baseStart_1249010 : Nat := 118140960795 + 1249010 * 2 ^ 59
def prefixEnd_1249010 : Nat := 4983230072969 + 3 ^ 40 * 1249010 * 2
def baseEnd_1249010 : Nat := 427561648181508984220609

theorem tailTrace_1249010 : CollatzResearch.WordTrace tailWord_1249010 prefixEnd_1249010 427561648181508984220609 := by
  unfold tailWord_1249010
  simp only [CollatzResearch.WordTrace]
  refine ⟨11388784301264389692580121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30370091470038372513546989 11388784301264389692580121)
  ·
    refine ⟨8541588225948292269435091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11388784301264389692580121 8541588225948292269435091)
    ·
      refine ⟨12812382338922438404152637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8541588225948292269435091 12812382338922438404152637)
      ·
        refine ⟨4804643377095914401557239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12812382338922438404152637 4804643377095914401557239)
        ·
          refine ⟨7206965065643871602335859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4804643377095914401557239 7206965065643871602335859)
          ·
            refine ⟨10810447598465807403503789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7206965065643871602335859 10810447598465807403503789)
            ·
              refine ⟨4053917849424677776313921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10810447598465807403503789 4053917849424677776313921)
              ·
                refine ⟨3040438387068508332235441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4053917849424677776313921 3040438387068508332235441)
                ·
                  refine ⟨2280328790301381249176581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3040438387068508332235441 2280328790301381249176581)
                  ·
                    refine ⟨427561648181508984220609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2280328790301381249176581 427561648181508984220609)
                    ·
                      rfl

theorem cell22_1249010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_1249010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1249010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1249010 prefixEnd_1249010 := by exact prefixLift 1249010
  have htrace : WordTrace (prefixWord ++ tailWord_1249010) baseStart_1249010 baseEnd_1249010 := by
    simpa [prefixWord, tailWord_1249010, baseEnd_1249010] using wordTrace_append hprefix tailTrace_1249010
  have hstable : (prefixWord ++ tailWord_1249010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249010).length < 2 ^ (prefixWord ++ tailWord_1249010).sum := by decide
  have hdescent : baseEnd_1249010 < baseStart_1249010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249014 : List Nat := [5, 1, 1, 1, 1, 4, 3, 2, 4]
def baseStart_1249014 : Nat := 118140960795 + 1249014 * 2 ^ 59
def prefixEnd_1249014 : Nat := 4983230072969 + 3 ^ 40 * 1249014 * 2
def baseEnd_1249014 : Nat := 142521005821084769040199

theorem tailTrace_1249014 : CollatzResearch.WordTrace tailWord_1249014 prefixEnd_1249014 142521005821084769040199 := by
  unfold tailWord_1249014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2847205193565191715841631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30370188731362044968977397 2847205193565191715841631)
  ·
    refine ⟨4270807790347787573762447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2847205193565191715841631 4270807790347787573762447)
    ·
      refine ⟨6406211685521681360643671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4270807790347787573762447 6406211685521681360643671)
      ·
        refine ⟨9609317528282522040965507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6406211685521681360643671 9609317528282522040965507)
        ·
          refine ⟨14413976292423783061448261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9609317528282522040965507 14413976292423783061448261)
          ·
            refine ⟨2702620554829459324021549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14413976292423783061448261 2702620554829459324021549)
            ·
              refine ⟨1013482708061047246508081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2702620554829459324021549 1013482708061047246508081)
              ·
                refine ⟨760112031045785434881061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1013482708061047246508081 760112031045785434881061)
                ·
                  refine ⟨142521005821084769040199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 760112031045785434881061 142521005821084769040199)
                  ·
                    rfl

theorem cell22_1249014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_1249014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1249014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1249014 prefixEnd_1249014 := by exact prefixLift 1249014
  have htrace : WordTrace (prefixWord ++ tailWord_1249014) baseStart_1249014 baseEnd_1249014 := by
    simpa [prefixWord, tailWord_1249014, baseEnd_1249014] using wordTrace_append hprefix tailTrace_1249014
  have hstable : (prefixWord ++ tailWord_1249014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249014).length < 2 ^ (prefixWord ++ tailWord_1249014).sum := by decide
  have hdescent : baseEnd_1249014 < baseStart_1249014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249074 : List Nat := [3, 2, 1, 1, 3, 3, 1, 4, 1, 3]
def baseStart_1249074 : Nat := 118140960795 + 1249074 * 2 ^ 59
def prefixEnd_1249074 : Nat := 4983230072969 + 3 ^ 40 * 1249074 * 2
def baseEnd_1249074 : Nat := 427583556689434150620413

theorem tailTrace_1249074 : CollatzResearch.WordTrace tailWord_1249074 prefixEnd_1249074 427583556689434150620413 := by
  unfold tailWord_1249074
  simp only [CollatzResearch.WordTrace]
  refine ⟨11389367869206424425162569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30371647651217131800433517 11389367869206424425162569)
  ·
    refine ⟨8542025901904818318871927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11389367869206424425162569 8542025901904818318871927)
    ·
      refine ⟨12813038852857227478307891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8542025901904818318871927 12813038852857227478307891)
      ·
        refine ⟨19219558279285841217461837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12813038852857227478307891 19219558279285841217461837)
        ·
          refine ⟨7207334354732190456548189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19219558279285841217461837 7207334354732190456548189)
          ·
            refine ⟨2702750383024571421205571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7207334354732190456548189 2702750383024571421205571)
            ·
              refine ⟨4054125574536857131808357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2702750383024571421205571 4054125574536857131808357)
              ·
                refine ⟨760148545225660712214067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4054125574536857131808357 760148545225660712214067)
                ·
                  refine ⟨1140222817838491068321101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 760148545225660712214067 1140222817838491068321101)
                  ·
                    refine ⟨427583556689434150620413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1140222817838491068321101 427583556689434150620413)
                    ·
                      rfl

theorem cell22_1249074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 4, 1, 3].length) (baseStart_1249074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1249074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1249074 prefixEnd_1249074 := by exact prefixLift 1249074
  have htrace : WordTrace (prefixWord ++ tailWord_1249074) baseStart_1249074 baseEnd_1249074 := by
    simpa [prefixWord, tailWord_1249074, baseEnd_1249074] using wordTrace_append hprefix tailTrace_1249074
  have hstable : (prefixWord ++ tailWord_1249074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249074).length < 2 ^ (prefixWord ++ tailWord_1249074).sum := by decide
  have hdescent : baseEnd_1249074 < baseStart_1249074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249085 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 1, 7]
def baseStart_1249085 : Nat := 118140960795 + 1249085 * 2 ^ 59
def prefixEnd_1249085 : Nat := 4983230072969 + 3 ^ 40 * 1249085 * 2
def baseEnd_1249085 : Nat := 427587322214233788595379

theorem tailTrace_1249085 : CollatzResearch.WordTrace tailWord_1249085 prefixEnd_1249085 427587322214233788595379 := by
  unfold tailWord_1249085
  simp only [CollatzResearch.WordTrace]
  refine ⟨45557872679785846579300709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30371915119857231052867139 45557872679785846579300709)
  ·
    refine ⟨8542101127459846233618883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45557872679785846579300709 8542101127459846233618883)
    ·
      refine ⟨12813151691189769350428325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8542101127459846233618883 12813151691189769350428325)
      ·
        refine ⟨2402465942098081753205311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12813151691189769350428325 2402465942098081753205311)
        ·
          refine ⟨3603698913147122629807967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2402465942098081753205311 3603698913147122629807967)
          ·
            refine ⟨5405548369720683944711951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3603698913147122629807967 5405548369720683944711951)
            ·
              refine ⟨8108322554581025917067927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5405548369720683944711951 8108322554581025917067927)
              ·
                refine ⟨12162483831871538875601891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8108322554581025917067927 12162483831871538875601891)
                ·
                  refine ⟨18243725747807308313402837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12162483831871538875601891 18243725747807308313402837)
                  ·
                    refine ⟨427587322214233788595379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18243725747807308313402837 427587322214233788595379)
                    ·
                      rfl

theorem cell22_1249085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_1249085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1249085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1249085 prefixEnd_1249085 := by exact prefixLift 1249085
  have htrace : WordTrace (prefixWord ++ tailWord_1249085) baseStart_1249085 baseEnd_1249085 := by
    simpa [prefixWord, tailWord_1249085, baseEnd_1249085] using wordTrace_append hprefix tailTrace_1249085
  have hstable : (prefixWord ++ tailWord_1249085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249085).length < 2 ^ (prefixWord ++ tailWord_1249085).sum := by decide
  have hdescent : baseEnd_1249085 < baseStart_1249085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249132 : List Nat := [2, 2, 1, 1, 4, 2, 2, 4, 4]
def baseStart_1249132 : Nat := 118140960795 + 1249132 * 2 ^ 59
def prefixEnd_1249132 : Nat := 4983230072969 + 3 ^ 40 * 1249132 * 2
def baseEnd_1249132 : Nat := 142534470424913777556745

theorem tailTrace_1249132 : CollatzResearch.WordTrace tailWord_1249132 prefixEnd_1249132 142534470424913777556745 := by
  unfold tailWord_1249132
  simp only [CollatzResearch.WordTrace]
  refine ⟨22779793455307786803130825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30373057940410382404174433 22779793455307786803130825)
  ·
    refine ⟨17084845091480840102348119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22779793455307786803130825 17084845091480840102348119)
    ·
      refine ⟨25627267637221260153522179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17084845091480840102348119 25627267637221260153522179)
      ·
        refine ⟨38440901455831890230283269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25627267637221260153522179 38440901455831890230283269)
        ·
          refine ⟨7207669022968479418178113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38440901455831890230283269 7207669022968479418178113)
          ·
            refine ⟨5405751767226359563633585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7207669022968479418178113 5405751767226359563633585)
            ·
              refine ⟨4054313825419769672725189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5405751767226359563633585 4054313825419769672725189)
              ·
                refine ⟨760183842266206813635973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4054313825419769672725189 760183842266206813635973)
                ·
                  refine ⟨142534470424913777556745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 760183842266206813635973 142534470424913777556745)
                  ·
                    rfl

theorem cell22_1249132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 4, 4].length) (baseStart_1249132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1249132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1249132 prefixEnd_1249132 := by exact prefixLift 1249132
  have htrace : WordTrace (prefixWord ++ tailWord_1249132) baseStart_1249132 baseEnd_1249132 := by
    simpa [prefixWord, tailWord_1249132, baseEnd_1249132] using wordTrace_append hprefix tailTrace_1249132
  have hstable : (prefixWord ++ tailWord_1249132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249132).length < 2 ^ (prefixWord ++ tailWord_1249132).sum := by decide
  have hdescent : baseEnd_1249132 < baseStart_1249132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249299 : List Nat := [1, 1, 1, 2, 1, 4, 5, 2, 2, 3]
def baseStart_1249299 : Nat := 118140960795 + 1249299 * 2 ^ 59
def prefixEnd_1249299 : Nat := 4983230072969 + 3 ^ 40 * 1249299 * 2
def baseEnd_1249299 : Nat := 427660578787608563744723

theorem tailTrace_1249299 : CollatzResearch.WordTrace tailWord_1249299 prefixEnd_1249299 427660578787608563744723 := by
  unfold tailWord_1249299
  simp only [CollatzResearch.WordTrace]
  refine ⟨45565677901010561127590951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30377118600673707418393967 45565677901010561127590951)
  ·
    refine ⟨68348516851515841691386427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45565677901010561127590951 68348516851515841691386427)
    ·
      refine ⟨102522775277273762537079641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68348516851515841691386427 102522775277273762537079641)
      ·
        refine ⟨76892081457955321902809731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102522775277273762537079641 76892081457955321902809731)
        ·
          refine ⟨115338122186932982854214597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76892081457955321902809731 115338122186932982854214597)
          ·
            refine ⟨21625897910049934285165237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115338122186932982854214597 21625897910049934285165237)
            ·
              refine ⟨2027427929067181339234241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21625897910049934285165237 2027427929067181339234241)
              ·
                refine ⟨1520570946800386004425681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2027427929067181339234241 1520570946800386004425681)
                ·
                  refine ⟨1140428210100289503319261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1520570946800386004425681 1140428210100289503319261)
                  ·
                    refine ⟨427660578787608563744723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1140428210100289503319261 427660578787608563744723)
                    ·
                      rfl

theorem cell22_1249299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 2, 3].length) (baseStart_1249299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1249299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1249299 prefixEnd_1249299 := by exact prefixLift 1249299
  have htrace : WordTrace (prefixWord ++ tailWord_1249299) baseStart_1249299 baseEnd_1249299 := by
    simpa [prefixWord, tailWord_1249299, baseEnd_1249299] using wordTrace_append hprefix tailTrace_1249299
  have hstable : (prefixWord ++ tailWord_1249299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249299).length < 2 ^ (prefixWord ++ tailWord_1249299).sum := by decide
  have hdescent : baseEnd_1249299 < baseStart_1249299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249316 : List Nat := [2, 3, 1, 4, 2, 2, 1, 1, 1, 5]
def baseStart_1249316 : Nat := 118140960795 + 1249316 * 2 ^ 59
def prefixEnd_1249316 : Nat := 4983230072969 + 3 ^ 40 * 1249316 * 2
def baseEnd_1249316 : Nat := 427666398235026186069671

theorem tailTrace_1249316 : CollatzResearch.WordTrace tailWord_1249316 prefixEnd_1249316 427666398235026186069671 := by
  unfold tailWord_1249316
  simp only [CollatzResearch.WordTrace]
  refine ⟨22783148970974486515479901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30377531961299315353973201 22783148970974486515479901)
  ·
    refine ⟨8543680864115432443304963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22783148970974486515479901 8543680864115432443304963)
    ·
      refine ⟨12815521296173148664957445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8543680864115432443304963 12815521296173148664957445)
      ·
        refine ⟨2402910243032465374679521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12815521296173148664957445 2402910243032465374679521)
        ·
          refine ⟨1802182682274349031009641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2402910243032465374679521 1802182682274349031009641)
          ·
            refine ⟨1351637011705761773257231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1802182682274349031009641 1351637011705761773257231)
            ·
              refine ⟨2027455517558642659885847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1351637011705761773257231 2027455517558642659885847)
              ·
                refine ⟨3041183276337963989828771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2027455517558642659885847 3041183276337963989828771)
                ·
                  refine ⟨4561774914506945984743157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3041183276337963989828771 4561774914506945984743157)
                  ·
                    refine ⟨427666398235026186069671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4561774914506945984743157 427666398235026186069671)
                    ·
                      rfl

theorem cell22_1249316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_1249316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1249316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1249316 prefixEnd_1249316 := by exact prefixLift 1249316
  have htrace : WordTrace (prefixWord ++ tailWord_1249316) baseStart_1249316 baseEnd_1249316 := by
    simpa [prefixWord, tailWord_1249316, baseEnd_1249316] using wordTrace_append hprefix tailTrace_1249316
  have hstable : (prefixWord ++ tailWord_1249316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249316).length < 2 ^ (prefixWord ++ tailWord_1249316).sum := by decide
  have hdescent : baseEnd_1249316 < baseStart_1249316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249327 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 5, 3]
def baseStart_1249327 : Nat := 118140960795 + 1249327 * 2 ^ 59
def prefixEnd_1249327 : Nat := 4983230072969 + 3 ^ 40 * 1249327 * 2
def baseEnd_1249327 : Nat := 427670163759825824044637

theorem tailTrace_1249327 : CollatzResearch.WordTrace tailWord_1249327 prefixEnd_1249327 427670163759825824044637 := by
  unfold tailWord_1249327
  simp only [CollatzResearch.WordTrace]
  refine ⟨45566699144909121909610235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30377799429939414606406823 45566699144909121909610235)
  ·
    refine ⟨68350048717363682864415353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45566699144909121909610235 68350048717363682864415353)
    ·
      refine ⟨51262536538022762148311515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68350048717363682864415353 51262536538022762148311515)
      ·
        refine ⟨76893804807034143222467273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51262536538022762148311515 76893804807034143222467273)
        ·
          refine ⟨57670353605275607416850455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76893804807034143222467273 57670353605275607416850455)
          ·
            refine ⟨86505530407913411125275683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57670353605275607416850455 86505530407913411125275683)
            ·
              refine ⟨129758295611870116687913525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86505530407913411125275683 129758295611870116687913525)
              ·
                refine ⟨12164840213612823439491893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 129758295611870116687913525 12164840213612823439491893)
                ·
                  refine ⟨1140453770026202197452365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12164840213612823439491893 1140453770026202197452365)
                  ·
                    refine ⟨427670163759825824044637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1140453770026202197452365 427670163759825824044637)
                    ·
                      rfl

theorem cell22_1249327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 5, 3].length) (baseStart_1249327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1249327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1249327 prefixEnd_1249327 := by exact prefixLift 1249327
  have htrace : WordTrace (prefixWord ++ tailWord_1249327) baseStart_1249327 baseEnd_1249327 := by
    simpa [prefixWord, tailWord_1249327, baseEnd_1249327] using wordTrace_append hprefix tailTrace_1249327
  have hstable : (prefixWord ++ tailWord_1249327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249327).length < 2 ^ (prefixWord ++ tailWord_1249327).sum := by decide
  have hdescent : baseEnd_1249327 < baseStart_1249327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249329 : List Nat := [1, 2, 2, 3, 1, 5, 2, 6]
def baseStart_1249329 : Nat := 118140960795 + 1249329 * 2 ^ 59
def prefixEnd_1249329 : Nat := 4983230072969 + 3 ^ 40 * 1249329 * 2
def baseEnd_1249329 : Nat := 47518983155633165054959

theorem tailTrace_1249329 : CollatzResearch.WordTrace tailWord_1249329 prefixEnd_1249329 47518983155633165054959 := by
  unfold tailWord_1249329
  simp only [CollatzResearch.WordTrace]
  refine ⟨45566772090901876251183041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30377848060601250834122027 45566772090901876251183041)
  ·
    refine ⟨34175079068176407188387281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45566772090901876251183041 34175079068176407188387281)
    ·
      refine ⟨25631309301132305391290461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34175079068176407188387281 25631309301132305391290461)
      ·
        refine ⟨9611740987924614521733923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25631309301132305391290461 9611740987924614521733923)
        ·
          refine ⟨14417611481886921782600885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9611740987924614521733923 14417611481886921782600885)
          ·
            refine ⟨1351651076426898917118833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14417611481886921782600885 1351651076426898917118833)
            ·
              refine ⟨1013738307320174187839125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1351651076426898917118833 1013738307320174187839125)
              ·
                refine ⟨47518983155633165054959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1013738307320174187839125 47518983155633165054959)
                ·
                  rfl

theorem cell22_1249329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 6].length) (baseStart_1249329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1249329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1249329 prefixEnd_1249329 := by exact prefixLift 1249329
  have htrace : WordTrace (prefixWord ++ tailWord_1249329) baseStart_1249329 baseEnd_1249329 := by
    simpa [prefixWord, tailWord_1249329, baseEnd_1249329] using wordTrace_append hprefix tailTrace_1249329
  have hstable : (prefixWord ++ tailWord_1249329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249329).length < 2 ^ (prefixWord ++ tailWord_1249329).sum := by decide
  have hdescent : baseEnd_1249329 < baseStart_1249329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249417 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 3, 5]
def baseStart_1249417 : Nat := 118140960795 + 1249417 * 2 ^ 59
def prefixEnd_1249417 : Nat := 4983230072969 + 3 ^ 40 * 1249417 * 2
def baseEnd_1249417 : Nat := 427700972599095589294361

theorem tailTrace_1249417 : CollatzResearch.WordTrace tailWord_1249417 prefixEnd_1249417 427700972599095589294361 := by
  unfold tailWord_1249417
  simp only [CollatzResearch.WordTrace]
  refine ⟨45569981714583067280386505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30379987809722044853591003 45569981714583067280386505)
  ·
    refine ⟨34177486285937300460289879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45569981714583067280386505 34177486285937300460289879)
    ·
      refine ⟨51266229428905950690434819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34177486285937300460289879 51266229428905950690434819)
      ·
        refine ⟨76899344143358926035652229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51266229428905950690434819 76899344143358926035652229)
        ·
          refine ⟨14418627026879798631684793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76899344143358926035652229 14418627026879798631684793)
          ·
            refine ⟨10813970270159848973763595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14418627026879798631684793 10813970270159848973763595)
            ·
              refine ⟨16220955405239773460645393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10813970270159848973763595 16220955405239773460645393)
              ·
                refine ⟨12165716553929830095484045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16220955405239773460645393 12165716553929830095484045)
                ·
                  refine ⟨4562143707723686285806517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12165716553929830095484045 4562143707723686285806517)
                  ·
                    refine ⟨427700972599095589294361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4562143707723686285806517 427700972599095589294361)
                    ·
                      rfl

theorem cell22_1249417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 5].length) (baseStart_1249417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1249417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1249417 prefixEnd_1249417 := by exact prefixLift 1249417
  have htrace : WordTrace (prefixWord ++ tailWord_1249417) baseStart_1249417 baseEnd_1249417 := by
    simpa [prefixWord, tailWord_1249417, baseEnd_1249417] using wordTrace_append hprefix tailTrace_1249417
  have hstable : (prefixWord ++ tailWord_1249417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249417).length < 2 ^ (prefixWord ++ tailWord_1249417).sum := by decide
  have hdescent : baseEnd_1249417 < baseStart_1249417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249453 : List Nat := [1, 5, 2, 1, 2, 2, 2, 3, 4]
def baseStart_1249453 : Nat := 118140960795 + 1249453 * 2 ^ 59
def prefixEnd_1249453 : Nat := 4983230072969 + 3 ^ 40 * 1249453 * 2
def baseEnd_1249453 : Nat := 142571098711601165131417

theorem tailTrace_1249453 : CollatzResearch.WordTrace tailWord_1249453 prefixEnd_1249453 142571098711601165131417 := by
  unfold tailWord_1249453
  simp only [CollatzResearch.WordTrace]
  refine ⟨45571294742452645428697013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30380863161635096952464675 45571294742452645428697013)
  ·
    refine ⟨4272308882104935508940345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45571294742452645428697013 4272308882104935508940345)
    ·
      refine ⟨3204231661578701631705259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4272308882104935508940345 3204231661578701631705259)
      ·
        refine ⟨4806347492368052447557889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3204231661578701631705259 4806347492368052447557889)
        ·
          refine ⟨3604760619276039335668417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4806347492368052447557889 3604760619276039335668417)
          ·
            refine ⟨2703570464457029501751313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3604760619276039335668417 2703570464457029501751313)
            ·
              refine ⟨2027677848342772126313485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2703570464457029501751313 2027677848342772126313485)
              ·
                refine ⟨760379193128539547367557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2027677848342772126313485 760379193128539547367557)
                ·
                  refine ⟨142571098711601165131417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 760379193128539547367557 142571098711601165131417)
                  ·
                    rfl

theorem cell22_1249453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_1249453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1249453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1249453 prefixEnd_1249453 := by exact prefixLift 1249453
  have htrace : WordTrace (prefixWord ++ tailWord_1249453) baseStart_1249453 baseEnd_1249453 := by
    simpa [prefixWord, tailWord_1249453, baseEnd_1249453] using wordTrace_append hprefix tailTrace_1249453
  have hstable : (prefixWord ++ tailWord_1249453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249453).length < 2 ^ (prefixWord ++ tailWord_1249453).sum := by decide
  have hdescent : baseEnd_1249453 < baseStart_1249453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249477 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 1, 8]
def baseStart_1249477 : Nat := 118140960795 + 1249477 * 2 ^ 59
def prefixEnd_1249477 : Nat := 4983230072969 + 3 ^ 40 * 1249477 * 2
def baseEnd_1249477 : Nat := 427721511825275432794177

theorem tailTrace_1249477 : CollatzResearch.WordTrace tailWord_1249477 prefixEnd_1249477 427721511825275432794177 := by
  unfold tailWord_1249477
  simp only [CollatzResearch.WordTrace]
  refine ⟨45572170094365697527570685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30381446729577131685047123 45572170094365697527570685)
  ·
    refine ⟨17089563785387136572839007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45572170094365697527570685 17089563785387136572839007)
    ·
      refine ⟨25634345678080704859258511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17089563785387136572839007 25634345678080704859258511)
      ·
        refine ⟨38451518517121057288887767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25634345678080704859258511 38451518517121057288887767)
        ·
          refine ⟨57677277775681585933331651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38451518517121057288887767 57677277775681585933331651)
          ·
            refine ⟨86515916663522378899997477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57677277775681585933331651 86515916663522378899997477)
            ·
              refine ⟨16221734374410446043749527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86515916663522378899997477 16221734374410446043749527)
              ·
                refine ⟨24332601561615669065624291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16221734374410446043749527 24332601561615669065624291)
                ·
                  refine ⟨36498902342423503598436437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24332601561615669065624291 36498902342423503598436437)
                  ·
                    refine ⟨427721511825275432794177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36498902342423503598436437 427721511825275432794177)
                    ·
                      rfl

theorem cell22_1249477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_1249477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1249477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1249477 prefixEnd_1249477 := by exact prefixLift 1249477
  have htrace : WordTrace (prefixWord ++ tailWord_1249477) baseStart_1249477 baseEnd_1249477 := by
    simpa [prefixWord, tailWord_1249477, baseEnd_1249477] using wordTrace_append hprefix tailTrace_1249477
  have hstable : (prefixWord ++ tailWord_1249477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249477).length < 2 ^ (prefixWord ++ tailWord_1249477).sum := by decide
  have hdescent : baseEnd_1249477 < baseStart_1249477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249496 : List Nat := [2, 1, 2, 2, 4, 1, 2, 2, 3, 3]
def baseStart_1249496 : Nat := 118140960795 + 1249496 * 2 ^ 59
def prefixEnd_1249496 : Nat := 4983230072969 + 3 ^ 40 * 1249496 * 2
def baseEnd_1249496 : Nat := 427728015913565716569119

theorem tailTrace_1249496 : CollatzResearch.WordTrace tailWord_1249496 prefixEnd_1249496 427728015913565716569119 := by
  unfold tailWord_1249496
  simp only [CollatzResearch.WordTrace]
  refine ⟨22786431540648431886256171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30381908720864575848341561 22786431540648431886256171)
  ·
    refine ⟨34179647310972647829384257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22786431540648431886256171 34179647310972647829384257)
    ·
      refine ⟨25634735483229485872038193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34179647310972647829384257 25634735483229485872038193)
      ·
        refine ⟨19226051612422114404028645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25634735483229485872038193 19226051612422114404028645)
        ·
          refine ⟨3604884677329146450755371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19226051612422114404028645 3604884677329146450755371)
          ·
            refine ⟨5407327015993719676133057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3604884677329146450755371 5407327015993719676133057)
            ·
              refine ⟨4055495261995289757099793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5407327015993719676133057 4055495261995289757099793)
              ·
                refine ⟨3041621446496467317824845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4055495261995289757099793 3041621446496467317824845)
                ·
                  refine ⟨1140608042436175244184317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3041621446496467317824845 1140608042436175244184317)
                  ·
                    refine ⟨427728015913565716569119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1140608042436175244184317 427728015913565716569119)
                    ·
                      rfl

theorem cell22_1249496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 3, 3].length) (baseStart_1249496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1249496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1249496 prefixEnd_1249496 := by exact prefixLift 1249496
  have htrace : WordTrace (prefixWord ++ tailWord_1249496) baseStart_1249496 baseEnd_1249496 := by
    simpa [prefixWord, tailWord_1249496, baseEnd_1249496] using wordTrace_append hprefix tailTrace_1249496
  have hstable : (prefixWord ++ tailWord_1249496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249496).length < 2 ^ (prefixWord ++ tailWord_1249496).sum := by decide
  have hdescent : baseEnd_1249496 < baseStart_1249496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249509 : List Nat := [1, 3, 1, 4, 2, 1, 1, 2, 7]
def baseStart_1249509 : Nat := 118140960795 + 1249509 * 2 ^ 59
def prefixEnd_1249509 : Nat := 4983230072969 + 3 ^ 40 * 1249509 * 2
def baseEnd_1249509 : Nat := 142577488693079338664693

theorem tailTrace_1249509 : CollatzResearch.WordTrace tailWord_1249509 prefixEnd_1249509 142577488693079338664693 := by
  unfold tailWord_1249509
  simp only [CollatzResearch.WordTrace]
  refine ⟨45573337230249766992735581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30382224820166511328490387 45573337230249766992735581)
  ·
    refine ⟨17090001461343662622275843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45573337230249766992735581 17090001461343662622275843)
    ·
      refine ⟨25635002192015493933413765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17090001461343662622275843 25635002192015493933413765)
      ·
        refine ⟨4806562911002905112515081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25635002192015493933413765 4806562911002905112515081)
        ·
          refine ⟨3604922183252178834386311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4806562911002905112515081 3604922183252178834386311)
          ·
            refine ⟨5407383274878268251579467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3604922183252178834386311 5407383274878268251579467)
            ·
              refine ⟨8111074912317402377369201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5407383274878268251579467 8111074912317402377369201)
              ·
                refine ⟨6083306184238051783026901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8111074912317402377369201 6083306184238051783026901)
                ·
                  refine ⟨142577488693079338664693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6083306184238051783026901 142577488693079338664693)
                  ·
                    rfl

theorem cell22_1249509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 7].length) (baseStart_1249509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1249509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1249509 prefixEnd_1249509 := by exact prefixLift 1249509
  have htrace : WordTrace (prefixWord ++ tailWord_1249509) baseStart_1249509 baseEnd_1249509 := by
    simpa [prefixWord, tailWord_1249509, baseEnd_1249509] using wordTrace_append hprefix tailTrace_1249509
  have hstable : (prefixWord ++ tailWord_1249509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249509).length < 2 ^ (prefixWord ++ tailWord_1249509).sum := by decide
  have hdescent : baseEnd_1249509 < baseStart_1249509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249530 : List Nat := [3, 1, 1, 1, 1, 6, 3, 2, 1, 3]
def baseStart_1249530 : Nat := 118140960795 + 1249530 * 2 ^ 59
def prefixEnd_1249530 : Nat := 4983230072969 + 3 ^ 40 * 1249530 * 2
def baseEnd_1249530 : Nat := 427739654808400961219015

theorem tailTrace_1249530 : CollatzResearch.WordTrace tailWord_1249530 prefixEnd_1249530 427739654808400961219015 := by
  unfold tailWord_1249530
  simp only [CollatzResearch.WordTrace]
  refine ⟨11393525790793421894812511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30382735442115791719500029 11393525790793421894812511)
  ·
    refine ⟨17090288686190132842218767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11393525790793421894812511 17090288686190132842218767)
    ·
      refine ⟨25635433029285199263328151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17090288686190132842218767 25635433029285199263328151)
      ·
        refine ⟨38453149543927798894992227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25635433029285199263328151 38453149543927798894992227)
        ·
          refine ⟨57679724315891698342488341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38453149543927798894992227 57679724315891698342488341)
          ·
            refine ⟨2703737077307423359804141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 57679724315891698342488341 2703737077307423359804141)
            ·
              refine ⟨1013901403990283759926553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2703737077307423359804141 1013901403990283759926553)
              ·
                refine ⟨760426052992712819944915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1013901403990283759926553 760426052992712819944915)
                ·
                  refine ⟨1140639079489069229917373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 760426052992712819944915 1140639079489069229917373)
                  ·
                    refine ⟨427739654808400961219015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1140639079489069229917373 427739654808400961219015)
                    ·
                      rfl

theorem cell22_1249530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 2, 1, 3].length) (baseStart_1249530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1249530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1249530 prefixEnd_1249530 := by exact prefixLift 1249530
  have htrace : WordTrace (prefixWord ++ tailWord_1249530) baseStart_1249530 baseEnd_1249530 := by
    simpa [prefixWord, tailWord_1249530, baseEnd_1249530] using wordTrace_append hprefix tailTrace_1249530
  have hstable : (prefixWord ++ tailWord_1249530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249530).length < 2 ^ (prefixWord ++ tailWord_1249530).sum := by decide
  have hdescent : baseEnd_1249530 < baseStart_1249530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249539 : List Nat := [1, 1, 1, 3, 2, 3, 2, 2, 3, 4]
def baseStart_1249539 : Nat := 118140960795 + 1249539 * 2 ^ 59
def prefixEnd_1249539 : Nat := 4983230072969 + 3 ^ 40 * 1249539 * 2
def baseEnd_1249539 : Nat := 427742735692327937743987

theorem tailTrace_1249539 : CollatzResearch.WordTrace tailWord_1249539 prefixEnd_1249539 427742735692327937743987 := by
  unfold tailWord_1249539
  simp only [CollatzResearch.WordTrace]
  refine ⟨45574431420141082116327671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30382954280094054744218447 45574431420141082116327671)
  ·
    refine ⟨68361647130211623174491507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45574431420141082116327671 68361647130211623174491507)
    ·
      refine ⟨102542470695317434761737261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68361647130211623174491507 102542470695317434761737261)
      ·
        refine ⟨38453426510744038035651473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102542470695317434761737261 38453426510744038035651473)
        ·
          refine ⟨28840069883058028526738605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38453426510744038035651473 28840069883058028526738605)
          ·
            refine ⟨10815026206146760697526977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28840069883058028526738605 10815026206146760697526977)
            ·
              refine ⟨8111269654610070523145233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10815026206146760697526977 8111269654610070523145233)
              ·
                refine ⟨6083452240957552892358925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8111269654610070523145233 6083452240957552892358925)
                ·
                  refine ⟨2281294590359082334634597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6083452240957552892358925 2281294590359082334634597)
                  ·
                    refine ⟨427742735692327937743987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2281294590359082334634597 427742735692327937743987)
                    ·
                      rfl

theorem cell22_1249539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 4].length) (baseStart_1249539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1249539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1249539 prefixEnd_1249539 := by exact prefixLift 1249539
  have htrace : WordTrace (prefixWord ++ tailWord_1249539) baseStart_1249539 baseEnd_1249539 := by
    simpa [prefixWord, tailWord_1249539, baseEnd_1249539] using wordTrace_append hprefix tailTrace_1249539
  have hstable : (prefixWord ++ tailWord_1249539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249539).length < 2 ^ (prefixWord ++ tailWord_1249539).sum := by decide
  have hdescent : baseEnd_1249539 < baseStart_1249539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249543 : List Nat := [1, 1, 4, 5, 1, 1, 1, 3, 5]
def baseStart_1249543 : Nat := 118140960795 + 1249543 * 2 ^ 59
def prefixEnd_1249543 : Nat := 4983230072969 + 3 ^ 40 * 1249543 * 2
def baseEnd_1249543 : Nat := 142581368324691086881325

theorem tailTrace_1249543 : CollatzResearch.WordTrace tailWord_1249543 prefixEnd_1249543 142581368324691086881325 := by
  unfold tailWord_1249543
  simp only [CollatzResearch.WordTrace]
  refine ⟨45574577312126590799473283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30383051541417727199648855 45574577312126590799473283)
  ·
    refine ⟨68361865968189886199209925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45574577312126590799473283 68361865968189886199209925)
    ·
      refine ⟨12817849869035603662351861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68361865968189886199209925 12817849869035603662351861)
      ·
        refine ⟨1201673425222087843345487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12817849869035603662351861 1201673425222087843345487)
        ·
          refine ⟨1802510137833131765018231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1201673425222087843345487 1802510137833131765018231)
          ·
            refine ⟨2703765206749697647527347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1802510137833131765018231 2703765206749697647527347)
            ·
              refine ⟨4055647810124546471291021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2703765206749697647527347 4055647810124546471291021)
              ·
                refine ⟨1520867928796704926734133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4055647810124546471291021 1520867928796704926734133)
                ·
                  refine ⟨142581368324691086881325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1520867928796704926734133 142581368324691086881325)
                  ·
                    rfl

theorem cell22_1249543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 5].length) (baseStart_1249543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1249543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1249543 prefixEnd_1249543 := by exact prefixLift 1249543
  have htrace : WordTrace (prefixWord ++ tailWord_1249543) baseStart_1249543 baseEnd_1249543 := by
    simpa [prefixWord, tailWord_1249543, baseEnd_1249543] using wordTrace_append hprefix tailTrace_1249543
  have hstable : (prefixWord ++ tailWord_1249543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249543).length < 2 ^ (prefixWord ++ tailWord_1249543).sum := by decide
  have hdescent : baseEnd_1249543 < baseStart_1249543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249569 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 3, 5]
def baseStart_1249569 : Nat := 118140960795 + 1249569 * 2 ^ 59
def prefixEnd_1249569 : Nat := 4983230072969 + 3 ^ 40 * 1249569 * 2
def baseEnd_1249569 : Nat := 427753005305417859493895

theorem tailTrace_1249569 : CollatzResearch.WordTrace tailWord_1249569 prefixEnd_1249569 427753005305417859493895 := by
  unfold tailWord_1249569
  simp only [CollatzResearch.WordTrace]
  refine ⟨45575525610032397239919761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30383683740021598159946507 45575525610032397239919761)
  ·
    refine ⟨34181644207524297929939821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45575525610032397239919761 34181644207524297929939821)
    ·
      refine ⟨12818116577821611723727433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34181644207524297929939821 12818116577821611723727433)
      ·
        refine ⟨9613587433366208792795575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12818116577821611723727433 9613587433366208792795575)
        ·
          refine ⟨14420381150049313189193363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9613587433366208792795575 14420381150049313189193363)
          ·
            refine ⟨21630571725073969783790045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14420381150049313189193363 21630571725073969783790045)
            ·
              refine ⟨8111464396902738668921267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21630571725073969783790045 8111464396902738668921267)
              ·
                refine ⟨12167196595354108003381901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8111464396902738668921267 12167196595354108003381901)
                ·
                  refine ⟨4562698723257790501268213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12167196595354108003381901 4562698723257790501268213)
                  ·
                    refine ⟨427753005305417859493895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4562698723257790501268213 427753005305417859493895)
                    ·
                      rfl

theorem cell22_1249569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_1249569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1249569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1249569 prefixEnd_1249569 := by exact prefixLift 1249569
  have htrace : WordTrace (prefixWord ++ tailWord_1249569) baseStart_1249569 baseEnd_1249569 := by
    simpa [prefixWord, tailWord_1249569, baseEnd_1249569] using wordTrace_append hprefix tailTrace_1249569
  have hstable : (prefixWord ++ tailWord_1249569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249569).length < 2 ^ (prefixWord ++ tailWord_1249569).sum := by decide
  have hdescent : baseEnd_1249569 < baseStart_1249569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249571 : List Nat := [1, 1, 1, 4, 2, 2, 2, 5, 4]
def baseStart_1249571 : Nat := 118140960795 + 1249571 * 2 ^ 59
def prefixEnd_1249571 : Nat := 4983230072969 + 3 ^ 40 * 1249571 * 2
def baseEnd_1249571 : Nat := 142584563315430173647963

theorem tailTrace_1249571 : CollatzResearch.WordTrace tailWord_1249571 prefixEnd_1249571 142584563315430173647963 := by
  unfold tailWord_1249571
  simp only [CollatzResearch.WordTrace]
  refine ⟨45575598556025151581492567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30383732370683434387661711 45575598556025151581492567)
  ·
    refine ⟨68363397834037727372238851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45575598556025151581492567 68363397834037727372238851)
    ·
      refine ⟨102545096751056591058358277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68363397834037727372238851 102545096751056591058358277)
      ·
        refine ⟨19227205640823110823442177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102545096751056591058358277 19227205640823110823442177)
        ·
          refine ⟨14420404230617333117581633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19227205640823110823442177 14420404230617333117581633)
          ·
            refine ⟨10815303172962999838186225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14420404230617333117581633 10815303172962999838186225)
            ·
              refine ⟨8111477379722249878639669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10815303172962999838186225 8111477379722249878639669)
              ·
                refine ⟨760451004348960926122469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8111477379722249878639669 760451004348960926122469)
                ·
                  refine ⟨142584563315430173647963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 760451004348960926122469 142584563315430173647963)
                  ·
                    rfl

theorem cell22_1249571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 5, 4].length) (baseStart_1249571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1249571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1249571 prefixEnd_1249571 := by exact prefixLift 1249571
  have htrace : WordTrace (prefixWord ++ tailWord_1249571) baseStart_1249571 baseEnd_1249571 := by
    simpa [prefixWord, tailWord_1249571, baseEnd_1249571] using wordTrace_append hprefix tailTrace_1249571
  have hstable : (prefixWord ++ tailWord_1249571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249571).length < 2 ^ (prefixWord ++ tailWord_1249571).sum := by decide
  have hdescent : baseEnd_1249571 < baseStart_1249571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249581 : List Nat := [1, 5, 3, 1, 3, 1, 2, 2, 1, 3]
def baseStart_1249581 : Nat := 118140960795 + 1249581 * 2 ^ 59
def prefixEnd_1249581 : Nat := 4983230072969 + 3 ^ 40 * 1249581 * 2
def baseEnd_1249581 : Nat := 427757113150653828193859

theorem tailTrace_1249581 : CollatzResearch.WordTrace tailWord_1249581 prefixEnd_1249581 427757113150653828193859 := by
  unfold tailWord_1249581
  simp only [CollatzResearch.WordTrace]
  refine ⟨45575963285988923289356597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30383975523992615526237731 45575963285988923289356597)
  ·
    refine ⟨4272746558061461558377181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45575963285988923289356597 4272746558061461558377181)
    ·
      refine ⟨1602279959273048084391443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4272746558061461558377181 1602279959273048084391443)
      ·
        refine ⟨2403419938909572126587165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1602279959273048084391443 2403419938909572126587165)
        ·
          refine ⟨901282477091089547470187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2403419938909572126587165 901282477091089547470187)
          ·
            refine ⟨1351923715636634321205281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 901282477091089547470187 1351923715636634321205281)
            ·
              refine ⟨1013942786727475740903961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1351923715636634321205281 1013942786727475740903961)
              ·
                refine ⟨760457090045606805677971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1013942786727475740903961 760457090045606805677971)
                ·
                  refine ⟨1140685635068410208516957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 760457090045606805677971 1140685635068410208516957)
                  ·
                    refine ⟨427757113150653828193859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1140685635068410208516957 427757113150653828193859)
                    ·
                      rfl

theorem cell22_1249581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_1249581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1249581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1249581 prefixEnd_1249581 := by exact prefixLift 1249581
  have htrace : WordTrace (prefixWord ++ tailWord_1249581) baseStart_1249581 baseEnd_1249581 := by
    simpa [prefixWord, tailWord_1249581, baseEnd_1249581] using wordTrace_append hprefix tailTrace_1249581
  have hstable : (prefixWord ++ tailWord_1249581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249581).length < 2 ^ (prefixWord ++ tailWord_1249581).sum := by decide
  have hdescent : baseEnd_1249581 < baseStart_1249581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249584 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 4, 4]
def baseStart_1249584 : Nat := 118140960795 + 1249584 * 2 ^ 59
def prefixEnd_1249584 : Nat := 4983230072969 + 3 ^ 40 * 1249584 * 2
def baseEnd_1249584 : Nat := 427758140111962820368849

theorem tailTrace_1249584 : CollatzResearch.WordTrace tailWord_1249584 prefixEnd_1249584 427758140111962820368849 := by
  unfold tailWord_1249584
  simp only [CollatzResearch.WordTrace]
  refine ⟨22788036352489027400857903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30384048469985369867810537 22788036352489027400857903)
  ·
    refine ⟨34182054528733541101286855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22788036352489027400857903 34182054528733541101286855)
    ·
      refine ⟨51273081793100311651930283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34182054528733541101286855 51273081793100311651930283)
      ·
        refine ⟨76909622689650467477895425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51273081793100311651930283 76909622689650467477895425)
        ·
          refine ⟨57682217017237850608421569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76909622689650467477895425 57682217017237850608421569)
          ·
            refine ⟨43261662762928387956316177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57682217017237850608421569 43261662762928387956316177)
            ·
              refine ⟨32446247072196290967237133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43261662762928387956316177 32446247072196290967237133)
              ·
                refine ⟨12167342652073609112713925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32446247072196290967237133 12167342652073609112713925)
                ·
                  refine ⟨2281376747263801708633861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12167342652073609112713925 2281376747263801708633861)
                  ·
                    refine ⟨427758140111962820368849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2281376747263801708633861 427758140111962820368849)
                    ·
                      rfl

theorem cell22_1249584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 4, 4].length) (baseStart_1249584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1249584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1249584 prefixEnd_1249584 := by exact prefixLift 1249584
  have htrace : WordTrace (prefixWord ++ tailWord_1249584) baseStart_1249584 baseEnd_1249584 := by
    simpa [prefixWord, tailWord_1249584, baseEnd_1249584] using wordTrace_append hprefix tailTrace_1249584
  have hstable : (prefixWord ++ tailWord_1249584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249584).length < 2 ^ (prefixWord ++ tailWord_1249584).sum := by decide
  have hdescent : baseEnd_1249584 < baseStart_1249584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249614 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 1, 9]
def baseStart_1249614 : Nat := 118140960795 + 1249614 * 2 ^ 59
def prefixEnd_1249614 : Nat := 4983230072969 + 3 ^ 40 * 1249614 * 2
def baseEnd_1249614 : Nat := 427768409725052742118757

theorem tailTrace_1249614 : CollatzResearch.WordTrace tailWord_1249614 prefixEnd_1249614 427768409725052742118757 := by
  unfold tailWord_1249614
  simp only [CollatzResearch.WordTrace]
  refine ⟨5697145861858671240663487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30384777929912913283538597 5697145861858671240663487)
  ·
    refine ⟨8545718792788006860995231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5697145861858671240663487 8545718792788006860995231)
    ·
      refine ⟨12818578189182010291492847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8545718792788006860995231 12818578189182010291492847)
      ·
        refine ⟨19227867283773015437239271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12818578189182010291492847 19227867283773015437239271)
        ·
          refine ⟨28841800925659523155858907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19227867283773015437239271 28841800925659523155858907)
          ·
            refine ⟨43262701388489284733788361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28841800925659523155858907 43262701388489284733788361)
            ·
              refine ⟨32447026041366963550341271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43262701388489284733788361 32447026041366963550341271)
              ·
                refine ⟨48670539062050445325511907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32447026041366963550341271 48670539062050445325511907)
                ·
                  refine ⟨73005808593075667988267861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48670539062050445325511907 73005808593075667988267861)
                  ·
                    refine ⟨427768409725052742118757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 73005808593075667988267861 427768409725052742118757)
                    ·
                      rfl

theorem cell22_1249614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_1249614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1249614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1249614 prefixEnd_1249614 := by exact prefixLift 1249614
  have htrace : WordTrace (prefixWord ++ tailWord_1249614) baseStart_1249614 baseEnd_1249614 := by
    simpa [prefixWord, tailWord_1249614, baseEnd_1249614] using wordTrace_append hprefix tailTrace_1249614
  have hstable : (prefixWord ++ tailWord_1249614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249614).length < 2 ^ (prefixWord ++ tailWord_1249614).sum := by decide
  have hdescent : baseEnd_1249614 < baseStart_1249614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249616 : List Nat := [2, 1, 1, 1, 1, 7, 3, 6]
def baseStart_1249616 : Nat := 118140960795 + 1249616 * 2 ^ 59
def prefixEnd_1249616 : Nat := 4983230072969 + 3 ^ 40 * 1249616 * 2
def baseEnd_1249616 : Nat := 47529899373991711507639

theorem tailTrace_1249616 : CollatzResearch.WordTrace tailWord_1249616 prefixEnd_1249616 47529899373991711507639 := by
  unfold tailWord_1249616
  simp only [CollatzResearch.WordTrace]
  refine ⟨22788619920431062133440351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30384826560574749511253801 22788619920431062133440351)
  ·
    refine ⟨34182929880646593200160527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22788619920431062133440351 34182929880646593200160527)
    ·
      refine ⟨51274394820969889800240791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34182929880646593200160527 51274394820969889800240791)
      ·
        refine ⟨76911592231454834700361187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51274394820969889800240791 76911592231454834700361187)
        ·
          refine ⟨115367388347182252050541781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76911592231454834700361187 115367388347182252050541781)
          ·
            refine ⟨2703923164387084032434573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 115367388347182252050541781 2703923164387084032434573)
            ·
              refine ⟨1013971186645156512162965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2703923164387084032434573 1013971186645156512162965)
              ·
                refine ⟨47529899373991711507639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1013971186645156512162965 47529899373991711507639)
                ·
                  rfl

theorem cell22_1249616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 6].length) (baseStart_1249616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1249616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1249616 prefixEnd_1249616 := by exact prefixLift 1249616
  have htrace : WordTrace (prefixWord ++ tailWord_1249616) baseStart_1249616 baseEnd_1249616 := by
    simpa [prefixWord, tailWord_1249616, baseEnd_1249616] using wordTrace_append hprefix tailTrace_1249616
  have hstable : (prefixWord ++ tailWord_1249616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249616).length < 2 ^ (prefixWord ++ tailWord_1249616).sum := by decide
  have hdescent : baseEnd_1249616 < baseStart_1249616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249648 : List Nat := [2, 1, 1, 1, 4, 4, 2, 1, 3, 3]
def baseStart_1249648 : Nat := 118140960795 + 1249648 * 2 ^ 59
def prefixEnd_1249648 : Nat := 4983230072969 + 3 ^ 40 * 1249648 * 2
def baseEnd_1249648 : Nat := 427780048619887986768653

theorem tailTrace_1249648 : CollatzResearch.WordTrace tailWord_1249648 prefixEnd_1249648 427780048619887986768653 := by
  unfold tailWord_1249648
  simp only [CollatzResearch.WordTrace]
  refine ⟨22789203488373096866022799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30385604651164129154697065 22789203488373096866022799)
  ·
    refine ⟨34183805232559645299034199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22789203488373096866022799 34183805232559645299034199)
    ·
      refine ⟨51275707848839467948551299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34183805232559645299034199 51275707848839467948551299)
      ·
        refine ⟨76913561773259201922826949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51275707848839467948551299 76913561773259201922826949)
        ·
          refine ⟨14421292832486100360530053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76913561773259201922826949 14421292832486100360530053)
          ·
            refine ⟨2703992406091143817599385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14421292832486100360530053 2703992406091143817599385)
            ·
              refine ⟨2027994304568357863199539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2703992406091143817599385 2027994304568357863199539)
              ·
                refine ⟨3041991456852536794799309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2027994304568357863199539 3041991456852536794799309)
                ·
                  refine ⟨1140746796319701298049741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3041991456852536794799309 1140746796319701298049741)
                  ·
                    refine ⟨427780048619887986768653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1140746796319701298049741 427780048619887986768653)
                    ·
                      rfl

theorem cell22_1249648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 3, 3].length) (baseStart_1249648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1249648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1249648 prefixEnd_1249648 := by exact prefixLift 1249648
  have htrace : WordTrace (prefixWord ++ tailWord_1249648) baseStart_1249648 baseEnd_1249648 := by
    simpa [prefixWord, tailWord_1249648, baseEnd_1249648] using wordTrace_append hprefix tailTrace_1249648
  have hstable : (prefixWord ++ tailWord_1249648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249648).length < 2 ^ (prefixWord ++ tailWord_1249648).sum := by decide
  have hdescent : baseEnd_1249648 < baseStart_1249648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249654 : List Nat := [5, 1, 1, 4, 1, 1, 3, 1, 2, 3]
def baseStart_1249654 : Nat := 118140960795 + 1249654 * 2 ^ 59
def prefixEnd_1249654 : Nat := 4983230072969 + 3 ^ 40 * 1249654 * 2
def baseEnd_1249654 : Nat := 427782102542505971118635

theorem tailTrace_1249654 : CollatzResearch.WordTrace tailWord_1249654 prefixEnd_1249654 427782102542505971118635 := by
  unfold tailWord_1249654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2848664113420278547297751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30385750543149637837842677 2848664113420278547297751)
  ·
    refine ⟨4272996170130417820946627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2848664113420278547297751 4272996170130417820946627)
    ·
      refine ⟨6409494255195626731419941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4272996170130417820946627 6409494255195626731419941)
      ·
        refine ⟨1201780172849180012141239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6409494255195626731419941 1201780172849180012141239)
        ·
          refine ⟨1802670259273770018211859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1201780172849180012141239 1802670259273770018211859)
          ·
            refine ⟨2704005388910655027317789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1802670259273770018211859 2704005388910655027317789)
            ·
              refine ⟨1014002020841495635244171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2704005388910655027317789 1014002020841495635244171)
              ·
                refine ⟨1521003031262243452866257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1014002020841495635244171 1521003031262243452866257)
                ·
                  refine ⟨1140752273446682589649693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1521003031262243452866257 1140752273446682589649693)
                  ·
                    refine ⟨427782102542505971118635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1140752273446682589649693 427782102542505971118635)
                    ·
                      rfl

theorem cell22_1249654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_1249654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1249654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1249654 prefixEnd_1249654 := by exact prefixLift 1249654
  have htrace : WordTrace (prefixWord ++ tailWord_1249654) baseStart_1249654 baseEnd_1249654 := by
    simpa [prefixWord, tailWord_1249654, baseEnd_1249654] using wordTrace_append hprefix tailTrace_1249654
  have hstable : (prefixWord ++ tailWord_1249654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249654).length < 2 ^ (prefixWord ++ tailWord_1249654).sum := by decide
  have hdescent : baseEnd_1249654 < baseStart_1249654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249725 : List Nat := [1, 4, 1, 2, 2, 4, 1, 2, 1, 4]
def baseStart_1249725 : Nat := 118140960795 + 1249725 * 2 ^ 59
def prefixEnd_1249725 : Nat := 4983230072969 + 3 ^ 40 * 1249725 * 2
def baseEnd_1249725 : Nat := 427806407293485452593417

theorem tailTrace_1249725 : CollatzResearch.WordTrace tailWord_1249725 prefixEnd_1249725 427806407293485452593417 := by
  unfold tailWord_1249725
  simp only [CollatzResearch.WordTrace]
  refine ⟨45581215397467235882598629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30387476931644823921732419 45581215397467235882598629)
  ·
    refine ⟨8546477887025106727987243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45581215397467235882598629 8546477887025106727987243)
    ·
      refine ⟨12819716830537660091980865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8546477887025106727987243 12819716830537660091980865)
      ·
        refine ⟨9614787622903245068985649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12819716830537660091980865 9614787622903245068985649)
        ·
          refine ⟨7211090717177433801739237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9614787622903245068985649 7211090717177433801739237)
          ·
            refine ⟨1352079509470768837826107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7211090717177433801739237 1352079509470768837826107)
            ·
              refine ⟨2028119264206153256739161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1352079509470768837826107 2028119264206153256739161)
              ·
                refine ⟨1521089448154614942554371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2028119264206153256739161 1521089448154614942554371)
                ·
                  refine ⟨2281634172231922413831557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1521089448154614942554371 2281634172231922413831557)
                  ·
                    refine ⟨427806407293485452593417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2281634172231922413831557 427806407293485452593417)
                    ·
                      rfl

theorem cell22_1249725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_1249725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1249725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1249725 prefixEnd_1249725 := by exact prefixLift 1249725
  have htrace : WordTrace (prefixWord ++ tailWord_1249725) baseStart_1249725 baseEnd_1249725 := by
    simpa [prefixWord, tailWord_1249725, baseEnd_1249725] using wordTrace_append hprefix tailTrace_1249725
  have hstable : (prefixWord ++ tailWord_1249725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249725).length < 2 ^ (prefixWord ++ tailWord_1249725).sum := by decide
  have hdescent : baseEnd_1249725 < baseStart_1249725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249768 : List Nat := [2, 1, 4, 1, 1, 5, 1, 7]
def baseStart_1249768 : Nat := 118140960795 + 1249768 * 2 ^ 59
def prefixEnd_1249768 : Nat := 4983230072969 + 3 ^ 40 * 1249768 * 2
def baseEnd_1249768 : Nat := 47535680785805297085365

theorem tailTrace_1249768 : CollatzResearch.WordTrace tailWord_1249768 prefixEnd_1249768 47535680785805297085365 := by
  unfold tailWord_1249768
  simp only [CollatzResearch.WordTrace]
  refine ⟨22791391868155727113206979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30388522490874302817609305 22791391868155727113206979)
  ·
    refine ⟨34187087802233590669810469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22791391868155727113206979 34187087802233590669810469)
    ·
      refine ⟨6410078962918798250589463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34187087802233590669810469 6410078962918798250589463)
      ·
        refine ⟨9615118444378197375884195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6410078962918798250589463 9615118444378197375884195)
        ·
          refine ⟨14422677666567296063826293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9615118444378197375884195 14422677666567296063826293)
          ·
            refine ⟨1352126031240684005983715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14422677666567296063826293 1352126031240684005983715)
            ·
              refine ⟨2028189046861026008975573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1352126031240684005983715 2028189046861026008975573)
              ·
                refine ⟨47535680785805297085365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2028189046861026008975573 47535680785805297085365)
                ·
                  rfl

theorem cell22_1249768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 7].length) (baseStart_1249768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1249768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1249768 prefixEnd_1249768 := by exact prefixLift 1249768
  have htrace : WordTrace (prefixWord ++ tailWord_1249768) baseStart_1249768 baseEnd_1249768 := by
    simpa [prefixWord, tailWord_1249768, baseEnd_1249768] using wordTrace_append hprefix tailTrace_1249768
  have hstable : (prefixWord ++ tailWord_1249768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249768).length < 2 ^ (prefixWord ++ tailWord_1249768).sum := by decide
  have hdescent : baseEnd_1249768 < baseStart_1249768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249811 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 4, 5]
def baseStart_1249811 : Nat := 118140960795 + 1249811 * 2 ^ 59
def prefixEnd_1249811 : Nat := 4983230072969 + 3 ^ 40 * 1249811 * 2
def baseEnd_1249811 : Nat := 427835846851009894943153

theorem tailTrace_1249811 : CollatzResearch.WordTrace tailWord_1249811 prefixEnd_1249811 427835846851009894943153 := by
  unfold tailWord_1249811
  simp only [CollatzResearch.WordTrace]
  refine ⟨45584352075155672570229287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30389568050103781713486191 45584352075155672570229287)
  ·
    refine ⟨68376528112733508855343931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45584352075155672570229287 68376528112733508855343931)
    ·
      refine ⟨102564792169100263283015897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68376528112733508855343931 102564792169100263283015897)
      ·
        refine ⟨76923594126825197462261923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102564792169100263283015897 76923594126825197462261923)
        ·
          refine ⟨115385391190237796193392885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76923594126825197462261923 115385391190237796193392885)
          ·
            refine ⟨10817380424084793393130583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 115385391190237796193392885 10817380424084793393130583)
            ·
              refine ⟨16226070636127190089695875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10817380424084793393130583 16226070636127190089695875)
              ·
                refine ⟨24339105954190785134543813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16226070636127190089695875 24339105954190785134543813)
                ·
                  refine ⟨4563582366410772212726965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24339105954190785134543813 4563582366410772212726965)
                  ·
                    refine ⟨427835846851009894943153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4563582366410772212726965 427835846851009894943153)
                    ·
                      rfl

theorem cell22_1249811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 5].length) (baseStart_1249811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1249811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1249811 prefixEnd_1249811 := by exact prefixLift 1249811
  have htrace : WordTrace (prefixWord ++ tailWord_1249811) baseStart_1249811 baseEnd_1249811 := by
    simpa [prefixWord, tailWord_1249811, baseEnd_1249811] using wordTrace_append hprefix tailTrace_1249811
  have hstable : (prefixWord ++ tailWord_1249811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249811).length < 2 ^ (prefixWord ++ tailWord_1249811).sum := by decide
  have hdescent : baseEnd_1249811 < baseStart_1249811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249950 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_1249950 : Nat := 118140960795 + 1249950 * 2 ^ 59
def prefixEnd_1249950 : Nat := 4983230072969 + 3 ^ 40 * 1249950 * 2
def baseEnd_1249950 : Nat := 427883429391659865717727

theorem tailTrace_1249950 : CollatzResearch.WordTrace tailWord_1249950 prefixEnd_1249950 427883429391659865717727 := by
  unfold tailWord_1249950
  simp only [CollatzResearch.WordTrace]
  refine ⟨5698677727706512413692413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30392947881101399539692869 5698677727706512413692413)
  ·
    refine ⟨2137004147889942155134655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5698677727706512413692413 2137004147889942155134655)
    ·
      refine ⟨3205506221834913232701983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2137004147889942155134655 3205506221834913232701983)
      ·
        refine ⟨4808259332752369849052975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3205506221834913232701983 4808259332752369849052975)
        ·
          refine ⟨7212388999128554773579463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4808259332752369849052975 7212388999128554773579463)
          ·
            refine ⟨10818583498692832160369195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7212388999128554773579463 10818583498692832160369195)
            ·
              refine ⟨16227875248039248240553793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10818583498692832160369195 16227875248039248240553793)
              ·
                refine ⟨12170906436029436180415345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16227875248039248240553793 12170906436029436180415345)
                ·
                  refine ⟨9128179827022077135311509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12170906436029436180415345 9128179827022077135311509)
                  ·
                    refine ⟨427883429391659865717727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9128179827022077135311509 427883429391659865717727)
                    ·
                      rfl

theorem cell22_1249950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_1249950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1249950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1249950 prefixEnd_1249950 := by exact prefixLift 1249950
  have htrace : WordTrace (prefixWord ++ tailWord_1249950) baseStart_1249950 baseEnd_1249950 := by
    simpa [prefixWord, tailWord_1249950, baseEnd_1249950] using wordTrace_append hprefix tailTrace_1249950
  have hstable : (prefixWord ++ tailWord_1249950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249950).length < 2 ^ (prefixWord ++ tailWord_1249950).sum := by decide
  have hdescent : baseEnd_1249950 < baseStart_1249950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249952 : List Nat := [2, 1, 1, 4, 4, 1, 1, 2, 3, 3]
def baseStart_1249952 : Nat := 118140960795 + 1249952 * 2 ^ 59
def prefixEnd_1249952 : Nat := 4983230072969 + 3 ^ 40 * 1249952 * 2
def baseEnd_1249952 : Nat := 427884114032532527167721

theorem tailTrace_1249952 : CollatzResearch.WordTrace tailWord_1249952 prefixEnd_1249952 427884114032532527167721 := by
  unfold tailWord_1249952
  simp only [CollatzResearch.WordTrace]
  refine ⟨22794747383822426825556055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30392996511763235767408073 22794747383822426825556055)
  ·
    refine ⟨34192121075733640238334083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22794747383822426825556055 34192121075733640238334083)
    ·
      refine ⟨51288181613600460357501125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34192121075733640238334083 51288181613600460357501125)
      ·
        refine ⟨9616534052550086317031461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51288181613600460357501125 9616534052550086317031461)
        ·
          refine ⟨1803100134853141184443399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9616534052550086317031461 1803100134853141184443399)
          ·
            refine ⟨2704650202279711776665099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1803100134853141184443399 2704650202279711776665099)
            ·
              refine ⟨4056975303419567664997649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2704650202279711776665099 4056975303419567664997649)
              ·
                refine ⟨3042731477564675748748237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4056975303419567664997649 3042731477564675748748237)
                ·
                  refine ⟨1141024304086753405780589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3042731477564675748748237 1141024304086753405780589)
                  ·
                    refine ⟨427884114032532527167721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1141024304086753405780589 427884114032532527167721)
                    ·
                      rfl

theorem cell22_1249952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 3, 3].length) (baseStart_1249952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1249952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1249952 prefixEnd_1249952 := by exact prefixLift 1249952
  have htrace : WordTrace (prefixWord ++ tailWord_1249952) baseStart_1249952 baseEnd_1249952 := by
    simpa [prefixWord, tailWord_1249952, baseEnd_1249952] using wordTrace_append hprefix tailTrace_1249952
  have hstable : (prefixWord ++ tailWord_1249952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249952).length < 2 ^ (prefixWord ++ tailWord_1249952).sum := by decide
  have hdescent : baseEnd_1249952 < baseStart_1249952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250025 : List Nat := [1, 2, 1, 1, 1, 2, 5, 2, 4, 3]
def baseStart_1250025 : Nat := 118140960795 + 1250025 * 2 ^ 59
def prefixEnd_1250025 : Nat := 4983230072969 + 3 ^ 40 * 1250025 * 2
def baseEnd_1250025 : Nat := 427909103424384670092497

theorem tailTrace_1250025 : CollatzResearch.WordTrace tailWord_1250025 prefixEnd_1250025 427909103424384670092497 := by
  unfold tailWord_1250025
  simp only [CollatzResearch.WordTrace]
  refine ⟨45592157296380387118519529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30394771530920258079013019 45592157296380387118519529)
  ·
    refine ⟨34194117972285290338889647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45592157296380387118519529 34194117972285290338889647)
    ·
      refine ⟨51291176958427935508334471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34194117972285290338889647 51291176958427935508334471)
      ·
        refine ⟨76936765437641903262501707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51291176958427935508334471 76936765437641903262501707)
        ·
          refine ⟨115405148156462854893752561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76936765437641903262501707 115405148156462854893752561)
          ·
            refine ⟨86553861117347141170314421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115405148156462854893752561 86553861117347141170314421)
            ·
              refine ⟨8114424479751294484716977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86553861117347141170314421 8114424479751294484716977)
              ·
                refine ⟨6085818359813470863537733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8114424479751294484716977 6085818359813470863537733)
                ·
                  refine ⟨1141090942465025786913325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6085818359813470863537733 1141090942465025786913325)
                  ·
                    refine ⟨427909103424384670092497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1141090942465025786913325 427909103424384670092497)
                    ·
                      rfl

theorem cell22_1250025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 4, 3].length) (baseStart_1250025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250025 prefixEnd_1250025 := by exact prefixLift 1250025
  have htrace : WordTrace (prefixWord ++ tailWord_1250025) baseStart_1250025 baseEnd_1250025 := by
    simpa [prefixWord, tailWord_1250025, baseEnd_1250025] using wordTrace_append hprefix tailTrace_1250025
  have hstable : (prefixWord ++ tailWord_1250025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250025).length < 2 ^ (prefixWord ++ tailWord_1250025).sum := by decide
  have hdescent : baseEnd_1250025 < baseStart_1250025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250040 : List Nat := [2, 1, 2, 1, 1, 2, 5, 2, 2, 4]
def baseStart_1250040 : Nat := 118140960795 + 1250040 * 2 ^ 59
def prefixEnd_1250040 : Nat := 4983230072969 + 3 ^ 40 * 1250040 * 2
def baseEnd_1250040 : Nat := 427914238230929630967451

theorem tailTrace_1250040 : CollatzResearch.WordTrace tailWord_1250040 prefixEnd_1250040 427914238230929630967451 := by
  unfold tailWord_1250040
  simp only [CollatzResearch.WordTrace]
  refine ⟨22796352195663022340157787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30395136260884029786877049 22796352195663022340157787)
  ·
    refine ⟨34194528293494533510236681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22796352195663022340157787 34194528293494533510236681)
    ·
      refine ⟨25645896220120900132677511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34194528293494533510236681 25645896220120900132677511)
      ·
        refine ⟨38468844330181350199016267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25645896220120900132677511 38468844330181350199016267)
        ·
          refine ⟨57703266495272025298524401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38468844330181350199016267 57703266495272025298524401)
          ·
            refine ⟨43277449871454018973893301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57703266495272025298524401 43277449871454018973893301)
            ·
              refine ⟨4057260925448814278802497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43277449871454018973893301 4057260925448814278802497)
              ·
                refine ⟨3042945694086610709101873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4057260925448814278802497 3042945694086610709101873)
                ·
                  refine ⟨2282209270564958031826405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3042945694086610709101873 2282209270564958031826405)
                  ·
                    refine ⟨427914238230929630967451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2282209270564958031826405 427914238230929630967451)
                    ·
                      rfl

theorem cell22_1250040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_1250040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250040 prefixEnd_1250040 := by exact prefixLift 1250040
  have htrace : WordTrace (prefixWord ++ tailWord_1250040) baseStart_1250040 baseEnd_1250040 := by
    simpa [prefixWord, tailWord_1250040, baseEnd_1250040] using wordTrace_append hprefix tailTrace_1250040
  have hstable : (prefixWord ++ tailWord_1250040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250040).length < 2 ^ (prefixWord ++ tailWord_1250040).sum := by decide
  have hdescent : baseEnd_1250040 < baseStart_1250040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250044 : List Nat := [2, 2, 2, 1, 3, 3, 3, 2, 4]
def baseStart_1250044 : Nat := 118140960795 + 1250044 * 2 ^ 59
def prefixEnd_1250044 : Nat := 4983230072969 + 3 ^ 40 * 1250044 * 2
def baseEnd_1250044 : Nat := 142638535837558317955813

theorem tailTrace_1250044 : CollatzResearch.WordTrace tailWord_1250044 prefixEnd_1250044 142638535837558317955813 := by
  unfold tailWord_1250044
  simp only [CollatzResearch.WordTrace]
  refine ⟨22796425141655776681730593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30395233522207702242307457 22796425141655776681730593)
  ·
    refine ⟨17097318856241832511297945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22796425141655776681730593 17097318856241832511297945)
    ·
      refine ⟨12822989142181374383473459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17097318856241832511297945 12822989142181374383473459)
      ·
        refine ⟨19234483713272061575210189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12822989142181374383473459 19234483713272061575210189)
        ·
          refine ⟨7212931392477023090703821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19234483713272061575210189 7212931392477023090703821)
          ·
            refine ⟨2704849272178883659013933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7212931392477023090703821 2704849272178883659013933)
            ·
              refine ⟨1014318477067081372130225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2704849272178883659013933 1014318477067081372130225)
              ·
                refine ⟨760738857800311029097669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1014318477067081372130225 760738857800311029097669)
                ·
                  refine ⟨142638535837558317955813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 760738857800311029097669 142638535837558317955813)
                  ·
                    rfl

theorem cell22_1250044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 2, 4].length) (baseStart_1250044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250044 prefixEnd_1250044 := by exact prefixLift 1250044
  have htrace : WordTrace (prefixWord ++ tailWord_1250044) baseStart_1250044 baseEnd_1250044 := by
    simpa [prefixWord, tailWord_1250044, baseEnd_1250044] using wordTrace_append hprefix tailTrace_1250044
  have hstable : (prefixWord ++ tailWord_1250044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250044).length < 2 ^ (prefixWord ++ tailWord_1250044).sum := by decide
  have hdescent : baseEnd_1250044 < baseStart_1250044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250055 : List Nat := [1, 1, 4, 4, 1, 1, 1, 9]
def baseStart_1250055 : Nat := 118140960795 + 1250055 * 2 ^ 59
def prefixEnd_1250055 : Nat := 4983230072969 + 3 ^ 40 * 1250055 * 2
def baseEnd_1250055 : Nat := 47546597004163843538045

theorem tailTrace_1250055 : CollatzResearch.WordTrace tailWord_1250055 prefixEnd_1250055 47546597004163843538045 := by
  unfold tailWord_1250055
  simp only [CollatzResearch.WordTrace]
  refine ⟨45593251486271702242111619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30395500990847801494741079 45593251486271702242111619)
  ·
    refine ⟨68389877229407553363167429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45593251486271702242111619 68389877229407553363167429)
    ·
      refine ⟨12823101980513916255593893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68389877229407553363167429 12823101980513916255593893)
      ·
        refine ⟨2404331621346359297923855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12823101980513916255593893 2404331621346359297923855)
        ·
          refine ⟨3606497432019538946885783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2404331621346359297923855 3606497432019538946885783)
          ·
            refine ⟨5409746148029308420328675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3606497432019538946885783 5409746148029308420328675)
            ·
              refine ⟨8114619222043962630493013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5409746148029308420328675 8114619222043962630493013)
              ·
                refine ⟨47546597004163843538045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8114619222043962630493013 47546597004163843538045)
                ·
                  rfl

theorem cell22_1250055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 9].length) (baseStart_1250055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250055 prefixEnd_1250055 := by exact prefixLift 1250055
  have htrace : WordTrace (prefixWord ++ tailWord_1250055) baseStart_1250055 baseEnd_1250055 := by
    simpa [prefixWord, tailWord_1250055, baseEnd_1250055] using wordTrace_append hprefix tailTrace_1250055
  have hstable : (prefixWord ++ tailWord_1250055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250055).length < 2 ^ (prefixWord ++ tailWord_1250055).sum := by decide
  have hdescent : baseEnd_1250055 < baseStart_1250055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250093 : List Nat := [1, 5, 3, 2, 1, 1, 2, 2, 2, 3]
def baseStart_1250093 : Nat := 118140960795 + 1250093 * 2 ^ 59
def prefixEnd_1250093 : Nat := 4983230072969 + 3 ^ 40 * 1250093 * 2
def baseEnd_1250093 : Nat := 427932381214055159392289

theorem tailTrace_1250093 : CollatzResearch.WordTrace tailWord_1250093 prefixEnd_1250093 427932381214055159392289 := by
  unfold tailWord_1250093
  simp only [CollatzResearch.WordTrace]
  refine ⟨45594637460134034731994933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30396424973422689821329955 45594637460134034731994933)
  ·
    refine ⟨4274497261887565756124525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45594637460134034731994933 4274497261887565756124525)
    ·
      refine ⟨1602936473207837158546697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4274497261887565756124525 1602936473207837158546697)
      ·
        refine ⟨1202202354905877868910023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1602936473207837158546697 1202202354905877868910023)
        ·
          refine ⟨1803303532358816803365035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1202202354905877868910023 1803303532358816803365035)
          ·
            refine ⟨2704955298538225205047553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1803303532358816803365035 2704955298538225205047553)
            ·
              refine ⟨2028716473903668903785665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2704955298538225205047553 2028716473903668903785665)
              ·
                refine ⟨1521537355427751677839249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2028716473903668903785665 1521537355427751677839249)
                ·
                  refine ⟨1141153016570813758379437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1521537355427751677839249 1141153016570813758379437)
                  ·
                    refine ⟨427932381214055159392289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1141153016570813758379437 427932381214055159392289)
                    ·
                      rfl

theorem cell22_1250093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_1250093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250093 prefixEnd_1250093 := by exact prefixLift 1250093
  have htrace : WordTrace (prefixWord ++ tailWord_1250093) baseStart_1250093 baseEnd_1250093 := by
    simpa [prefixWord, tailWord_1250093, baseEnd_1250093] using wordTrace_append hprefix tailTrace_1250093
  have hstable : (prefixWord ++ tailWord_1250093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250093).length < 2 ^ (prefixWord ++ tailWord_1250093).sum := by decide
  have hdescent : baseEnd_1250093 < baseStart_1250093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250104 : List Nat := [2, 1, 2, 1, 3, 2, 3, 4, 1, 3]
def baseStart_1250104 : Nat := 118140960795 + 1250104 * 2 ^ 59
def prefixEnd_1250104 : Nat := 4983230072969 + 3 ^ 40 * 1250104 * 2
def baseEnd_1250104 : Nat := 427936146738854797367255

theorem tailTrace_1250104 : CollatzResearch.WordTrace tailWord_1250104 prefixEnd_1250104 427936146738854797367255 := by
  unfold tailWord_1250104
  simp only [CollatzResearch.WordTrace]
  refine ⟨22797519331547091805322683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30396692442062789073763577 22797519331547091805322683)
  ·
    refine ⟨34196278997320637707984025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22797519331547091805322683 34196278997320637707984025)
    ·
      refine ⟨25647209247990478280988019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34196278997320637707984025 25647209247990478280988019)
      ·
        refine ⟨38470813871985717421482029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25647209247990478280988019 38470813871985717421482029)
        ·
          refine ⟨14426555201994644033055761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38470813871985717421482029 14426555201994644033055761)
          ·
            refine ⟨10819916401495983024791821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14426555201994644033055761 10819916401495983024791821)
            ·
              refine ⟨4057468650560993634296933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10819916401495983024791821 4057468650560993634296933)
              ·
                refine ⟨760775371980186306430675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4057468650560993634296933 760775371980186306430675)
                ·
                  refine ⟨1141163057970279459646013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 760775371980186306430675 1141163057970279459646013)
                  ·
                    refine ⟨427936146738854797367255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1141163057970279459646013 427936146738854797367255)
                    ·
                      rfl

theorem cell22_1250104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 4, 1, 3].length) (baseStart_1250104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250104 prefixEnd_1250104 := by exact prefixLift 1250104
  have htrace : WordTrace (prefixWord ++ tailWord_1250104) baseStart_1250104 baseEnd_1250104 := by
    simpa [prefixWord, tailWord_1250104, baseEnd_1250104] using wordTrace_append hprefix tailTrace_1250104
  have hstable : (prefixWord ++ tailWord_1250104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250104).length < 2 ^ (prefixWord ++ tailWord_1250104).sum := by decide
  have hdescent : baseEnd_1250104 < baseStart_1250104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250115 : List Nat := [1, 1, 1, 3, 1, 4, 3, 1, 2, 5]
def baseStart_1250115 : Nat := 118140960795 + 1250115 * 2 ^ 59
def prefixEnd_1250115 : Nat := 4983230072969 + 3 ^ 40 * 1250115 * 2
def baseEnd_1250115 : Nat := 427939912263654435342221

theorem tailTrace_1250115 : CollatzResearch.WordTrace tailWord_1250115 prefixEnd_1250115 427939912263654435342221 := by
  unfold tailWord_1250115
  simp only [CollatzResearch.WordTrace]
  refine ⟨45595439866054332489295799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30396959910702888326197199 45595439866054332489295799)
  ·
    refine ⟨68393159799081498733943699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45595439866054332489295799 68393159799081498733943699)
    ·
      refine ⟨102589739698622248100915549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68393159799081498733943699 102589739698622248100915549)
      ·
        refine ⟨38471152386983343037843331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102589739698622248100915549 38471152386983343037843331)
        ·
          refine ⟨57706728580475014556764997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38471152386983343037843331 57706728580475014556764997)
          ·
            refine ⟨10820011608839065229393437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57706728580475014556764997 10820011608839065229393437)
            ·
              refine ⟨4057504353314649461022539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10820011608839065229393437 4057504353314649461022539)
              ·
                refine ⟨6086256529971974191533809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4057504353314649461022539 6086256529971974191533809)
                ·
                  refine ⟨4564692397478980643650357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6086256529971974191533809 4564692397478980643650357)
                  ·
                    refine ⟨427939912263654435342221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4564692397478980643650357 427939912263654435342221)
                    ·
                      rfl

theorem cell22_1250115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 5].length) (baseStart_1250115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250115 prefixEnd_1250115 := by exact prefixLift 1250115
  have htrace : WordTrace (prefixWord ++ tailWord_1250115) baseStart_1250115 baseEnd_1250115 := by
    simpa [prefixWord, tailWord_1250115, baseEnd_1250115] using wordTrace_append hprefix tailTrace_1250115
  have hstable : (prefixWord ++ tailWord_1250115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250115).length < 2 ^ (prefixWord ++ tailWord_1250115).sum := by decide
  have hdescent : baseEnd_1250115 < baseStart_1250115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250160 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 3, 5]
def baseStart_1250160 : Nat := 118140960795 + 1250160 * 2 ^ 59
def prefixEnd_1250160 : Nat := 4983230072969 + 3 ^ 40 * 1250160 * 2
def baseEnd_1250160 : Nat := 427955316683289317967083

theorem tailTrace_1250160 : CollatzResearch.WordTrace tailWord_1250160 prefixEnd_1250160 427955316683289317967083 := by
  unfold tailWord_1250160
  simp only [CollatzResearch.WordTrace]
  refine ⟨22798540575445652587341967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30398054100594203449789289 22798540575445652587341967)
  ·
    refine ⟨34197810863168478881012951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22798540575445652587341967 34197810863168478881012951)
    ·
      refine ⟨51296716294752718321519427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34197810863168478881012951 51296716294752718321519427)
      ·
        refine ⟨76945074442129077482279141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51296716294752718321519427 76945074442129077482279141)
        ·
          refine ⟨14427201457899202027927339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76945074442129077482279141 14427201457899202027927339)
          ·
            refine ⟨21640802186848803041891009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14427201457899202027927339 21640802186848803041891009)
            ·
              refine ⟨16230601640136602281418257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21640802186848803041891009 16230601640136602281418257)
              ·
                refine ⟨12172951230102451711063693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16230601640136602281418257 12172951230102451711063693)
                ·
                  refine ⟨4564856711288419391648885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12172951230102451711063693 4564856711288419391648885)
                  ·
                    refine ⟨427955316683289317967083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4564856711288419391648885 427955316683289317967083)
                    ·
                      rfl

theorem cell22_1250160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 3, 5].length) (baseStart_1250160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250160 prefixEnd_1250160 := by exact prefixLift 1250160
  have htrace : WordTrace (prefixWord ++ tailWord_1250160) baseStart_1250160 baseEnd_1250160 := by
    simpa [prefixWord, tailWord_1250160, baseEnd_1250160] using wordTrace_append hprefix tailTrace_1250160
  have hstable : (prefixWord ++ tailWord_1250160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250160).length < 2 ^ (prefixWord ++ tailWord_1250160).sum := by decide
  have hdescent : baseEnd_1250160 < baseStart_1250160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250175 : List Nat := [1, 1, 2, 2, 1, 1, 5, 2, 1, 6]
def baseStart_1250175 : Nat := 118140960795 + 1250175 * 2 ^ 59
def prefixEnd_1250175 : Nat := 4983230072969 + 3 ^ 40 * 1250175 * 2
def baseEnd_1250175 : Nat := 427960451489834278842037

theorem tailTrace_1250175 : CollatzResearch.WordTrace tailWord_1250175 prefixEnd_1250175 427960451489834278842037 := by
  unfold tailWord_1250175
  simp only [CollatzResearch.WordTrace]
  refine ⟨45597628245836962736479979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30398418830557975157653319 45597628245836962736479979)
  ·
    refine ⟨68396442368755444104719969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45597628245836962736479979 68396442368755444104719969)
    ·
      refine ⟨51297331776566583078539977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68396442368755444104719969 51297331776566583078539977)
      ·
        refine ⟨38472998832424937308904983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51297331776566583078539977 38472998832424937308904983)
        ·
          refine ⟨57709498248637405963357475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38472998832424937308904983 57709498248637405963357475)
          ·
            refine ⟨86564247372956108945036213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57709498248637405963357475 86564247372956108945036213)
            ·
              refine ⟨8115398191214635213597145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86564247372956108945036213 8115398191214635213597145)
              ·
                refine ⟨6086548643410976410197859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8115398191214635213597145 6086548643410976410197859)
                ·
                  refine ⟨9129822965116464615296789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6086548643410976410197859 9129822965116464615296789)
                  ·
                    refine ⟨427960451489834278842037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9129822965116464615296789 427960451489834278842037)
                    ·
                      rfl

theorem cell22_1250175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 6].length) (baseStart_1250175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250175 prefixEnd_1250175 := by exact prefixLift 1250175
  have htrace : WordTrace (prefixWord ++ tailWord_1250175) baseStart_1250175 baseEnd_1250175 := by
    simpa [prefixWord, tailWord_1250175, baseEnd_1250175] using wordTrace_append hprefix tailTrace_1250175
  have hstable : (prefixWord ++ tailWord_1250175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250175).length < 2 ^ (prefixWord ++ tailWord_1250175).sum := by decide
  have hdescent : baseEnd_1250175 < baseStart_1250175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250198 : List Nat := [5, 3, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_1250198 : Nat := 118140960795 + 1250198 * 2 ^ 59
def prefixEnd_1250198 : Nat := 4983230072969 + 3 ^ 40 * 1250198 * 2
def baseEnd_1250198 : Nat := 427968324859869885516967

theorem tailTrace_1250198 : CollatzResearch.WordTrace tailWord_1250198 prefixEnd_1250198 427968324859869885516967 := by
  unfold tailWord_1250198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2849904195297102354035453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30398978083169091776378165 2849904195297102354035453)
  ·
    refine ⟨1068714073236413382763295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2849904195297102354035453 1068714073236413382763295)
    ·
      refine ⟨1603071109854620074144943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1068714073236413382763295 1603071109854620074144943)
      ·
        refine ⟨2404606664781930111217415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1603071109854620074144943 2404606664781930111217415)
        ·
          refine ⟨3606909997172895166826123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2404606664781930111217415 3606909997172895166826123)
          ·
            refine ⟨5410364995759342750239185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3606909997172895166826123 5410364995759342750239185)
            ·
              refine ⟨4057773746819507062679389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5410364995759342750239185 4057773746819507062679389)
              ·
                refine ⟨1521665155057315148504771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4057773746819507062679389 1521665155057315148504771)
                ·
                  refine ⟨2282497732585972722757157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1521665155057315148504771 2282497732585972722757157)
                  ·
                    refine ⟨427968324859869885516967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2282497732585972722757157 427968324859869885516967)
                    ·
                      rfl

theorem cell22_1250198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_1250198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250198 prefixEnd_1250198 := by exact prefixLift 1250198
  have htrace : WordTrace (prefixWord ++ tailWord_1250198) baseStart_1250198 baseEnd_1250198 := by
    simpa [prefixWord, tailWord_1250198, baseEnd_1250198] using wordTrace_append hprefix tailTrace_1250198
  have hstable : (prefixWord ++ tailWord_1250198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250198).length < 2 ^ (prefixWord ++ tailWord_1250198).sum := by decide
  have hdescent : baseEnd_1250198 < baseStart_1250198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250207 : List Nat := [1, 1, 2, 5, 2, 3, 8]
def baseStart_1250207 : Nat := 118140960795 + 1250207 * 2 ^ 59
def prefixEnd_1250207 : Nat := 4983230072969 + 3 ^ 40 * 1250207 * 2
def baseEnd_1250207 : Nat := 15850792805325809705257

theorem tailTrace_1250207 : CollatzResearch.WordTrace tailWord_1250207 prefixEnd_1250207 15850792805325809705257 := by
  unfold tailWord_1250207
  simp only [CollatzResearch.WordTrace]
  refine ⟨45598795381721032201644875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30399196921147354801096583 45598795381721032201644875)
  ·
    refine ⟨68398193072581548302467313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45598795381721032201644875 68398193072581548302467313)
    ·
      refine ⟨51298644804436161226850485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68398193072581548302467313 51298644804436161226850485)
      ·
        refine ⟨4809247950415890115017233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51298644804436161226850485 4809247950415890115017233)
        ·
          refine ⟨3606935962811917586262925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4809247950415890115017233 3606935962811917586262925)
          ·
            refine ⟨1352600986054469094848597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3606935962811917586262925 1352600986054469094848597)
            ·
              refine ⟨15850792805325809705257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1352600986054469094848597 15850792805325809705257)
              ·
                rfl

theorem cell22_1250207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 8].length) (baseStart_1250207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250207 prefixEnd_1250207 := by exact prefixLift 1250207
  have htrace : WordTrace (prefixWord ++ tailWord_1250207) baseStart_1250207 baseEnd_1250207 := by
    simpa [prefixWord, tailWord_1250207, baseEnd_1250207] using wordTrace_append hprefix tailTrace_1250207
  have hstable : (prefixWord ++ tailWord_1250207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250207).length < 2 ^ (prefixWord ++ tailWord_1250207).sum := by decide
  have hdescent : baseEnd_1250207 < baseStart_1250207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250209 : List Nat := [1, 2, 3, 4, 1, 2, 1, 2, 2, 4]
def baseStart_1250209 : Nat := 118140960795 + 1250209 * 2 ^ 59
def prefixEnd_1250209 : Nat := 4983230072969 + 3 ^ 40 * 1250209 * 2
def baseEnd_1250209 : Nat := 427972090384669523491933

theorem tailTrace_1250209 : CollatzResearch.WordTrace tailWord_1250209 prefixEnd_1250209 427972090384669523491933 := by
  unfold tailWord_1250209
  simp only [CollatzResearch.WordTrace]
  refine ⟨45598868327713786543217681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30399245551809191028811787 45598868327713786543217681)
  ·
    refine ⟨34199151245785339907413261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45598868327713786543217681 34199151245785339907413261)
    ·
      refine ⟨12824681717169502465279973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34199151245785339907413261 12824681717169502465279973)
      ·
        refine ⟨2404627821969281712239995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12824681717169502465279973 2404627821969281712239995)
        ·
          refine ⟨3606941732953922568359993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2404627821969281712239995 3606941732953922568359993)
          ·
            refine ⟨2705206299715441926269995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3606941732953922568359993 2705206299715441926269995)
            ·
              refine ⟨4057809449573162889404993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2705206299715441926269995 4057809449573162889404993)
              ·
                refine ⟨3043357087179872167053745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4057809449573162889404993 3043357087179872167053745)
                ·
                  refine ⟨2282517815384904125290309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3043357087179872167053745 2282517815384904125290309)
                  ·
                    refine ⟨427972090384669523491933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2282517815384904125290309 427972090384669523491933)
                    ·
                      rfl

theorem cell22_1250209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_1250209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250209 prefixEnd_1250209 := by exact prefixLift 1250209
  have htrace : WordTrace (prefixWord ++ tailWord_1250209) baseStart_1250209 baseEnd_1250209 := by
    simpa [prefixWord, tailWord_1250209, baseEnd_1250209] using wordTrace_append hprefix tailTrace_1250209
  have hstable : (prefixWord ++ tailWord_1250209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250209).length < 2 ^ (prefixWord ++ tailWord_1250209).sum := by decide
  have hdescent : baseEnd_1250209 < baseStart_1250209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250220 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 1, 8]
def baseStart_1250220 : Nat := 118140960795 + 1250220 * 2 ^ 59
def prefixEnd_1250220 : Nat := 4983230072969 + 3 ^ 40 * 1250220 * 2
def baseEnd_1250220 : Nat := 427975855909469161466899

theorem tailTrace_1250220 : CollatzResearch.WordTrace tailWord_1250220 prefixEnd_1250220 427975855909469161466899 := by
  unfold tailWord_1250220
  simp only [CollatzResearch.WordTrace]
  refine ⟨22799634765336967710934057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30399513020449290281245409 22799634765336967710934057)
  ·
    refine ⟨17099726074002725783200543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22799634765336967710934057 17099726074002725783200543)
    ·
      refine ⟨25649589111004088674800815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17099726074002725783200543 25649589111004088674800815)
      ·
        refine ⟨38474383666506133012201223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25649589111004088674800815 38474383666506133012201223)
        ·
          refine ⟨57711575499759199518301835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38474383666506133012201223 57711575499759199518301835)
          ·
            refine ⟨86567363249638799277452753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57711575499759199518301835 86567363249638799277452753)
            ·
              refine ⟨64925522437229099458089565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86567363249638799277452753 64925522437229099458089565)
              ·
                refine ⟨24347070913960912296783587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64925522437229099458089565 24347070913960912296783587)
                ·
                  refine ⟨36520606370941368445175381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24347070913960912296783587 36520606370941368445175381)
                  ·
                    refine ⟨427975855909469161466899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36520606370941368445175381 427975855909469161466899)
                    ·
                      rfl

theorem cell22_1250220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_1250220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250220 prefixEnd_1250220 := by exact prefixLift 1250220
  have htrace : WordTrace (prefixWord ++ tailWord_1250220) baseStart_1250220 baseEnd_1250220 := by
    simpa [prefixWord, tailWord_1250220, baseEnd_1250220] using wordTrace_append hprefix tailTrace_1250220
  have hstable : (prefixWord ++ tailWord_1250220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250220).length < 2 ^ (prefixWord ++ tailWord_1250220).sum := by decide
  have hdescent : baseEnd_1250220 < baseStart_1250220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250228 : List Nat := [2, 5, 2, 1, 1, 2, 1, 3, 2, 3]
def baseStart_1250228 : Nat := 118140960795 + 1250228 * 2 ^ 59
def prefixEnd_1250228 : Nat := 4983230072969 + 3 ^ 40 * 1250228 * 2
def baseEnd_1250228 : Nat := 427978594472959807266875

theorem tailTrace_1250228 : CollatzResearch.WordTrace tailWord_1250228 prefixEnd_1250228 427978594472959807266875 := by
  unfold tailWord_1250228
  simp only [CollatzResearch.WordTrace]
  refine ⟨22799780657322476394079669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30399707543096635192106225 22799780657322476394079669)
  ·
    refine ⟨2137479436623982161944969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22799780657322476394079669 2137479436623982161944969)
    ·
      refine ⟨1603109577467986621458727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2137479436623982161944969 1603109577467986621458727)
      ·
        refine ⟨2404664366201979932188091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1603109577467986621458727 2404664366201979932188091)
        ·
          refine ⟨3606996549302969898282137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2404664366201979932188091 3606996549302969898282137)
          ·
            refine ⟨2705247411977227423711603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3606996549302969898282137 2705247411977227423711603)
            ·
              refine ⟨4057871117965841135567405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2705247411977227423711603 4057871117965841135567405)
              ·
                refine ⟨1521701669237190425837777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4057871117965841135567405 1521701669237190425837777)
                ·
                  refine ⟨1141276251927892819378333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1521701669237190425837777 1141276251927892819378333)
                  ·
                    refine ⟨427978594472959807266875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1141276251927892819378333 427978594472959807266875)
                    ·
                      rfl

theorem cell22_1250228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_1250228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250228 prefixEnd_1250228 := by exact prefixLift 1250228
  have htrace : WordTrace (prefixWord ++ tailWord_1250228) baseStart_1250228 baseEnd_1250228 := by
    simpa [prefixWord, tailWord_1250228, baseEnd_1250228] using wordTrace_append hprefix tailTrace_1250228
  have hstable : (prefixWord ++ tailWord_1250228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250228).length < 2 ^ (prefixWord ++ tailWord_1250228).sum := by decide
  have hdescent : baseEnd_1250228 < baseStart_1250228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250269 : List Nat := [1, 4, 3, 1, 2, 1, 1, 4, 5]
def baseStart_1250269 : Nat := 118140960795 + 1250269 * 2 ^ 59
def prefixEnd_1250269 : Nat := 4983230072969 + 3 ^ 40 * 1250269 * 2
def baseEnd_1250269 : Nat := 142664209870283122330583

theorem tailTrace_1250269 : CollatzResearch.WordTrace tailWord_1250269 prefixEnd_1250269 142664209870283122330583 := by
  unfold tailWord_1250269
  simp only [CollatzResearch.WordTrace]
  refine ⟨45601056707496416790401861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30400704471664277860267907 45601056707496416790401861)
  ·
    refine ⟨8550198132655578148200349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45601056707496416790401861 8550198132655578148200349)
    ·
      refine ⟨3206324299745841805575131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8550198132655578148200349 3206324299745841805575131)
      ·
        refine ⟨4809486449618762708362697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3206324299745841805575131 4809486449618762708362697)
        ·
          refine ⟨3607114837214072031272023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4809486449618762708362697 3607114837214072031272023)
          ·
            refine ⟨5410672255821108046908035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3607114837214072031272023 5410672255821108046908035)
            ·
              refine ⟨8116008383731662070362053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5410672255821108046908035 8116008383731662070362053)
              ·
                refine ⟨1521751571949686638192885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8116008383731662070362053 1521751571949686638192885)
                ·
                  refine ⟨142664209870283122330583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1521751571949686638192885 142664209870283122330583)
                  ·
                    rfl

theorem cell22_1250269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_1250269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250269 prefixEnd_1250269 := by exact prefixLift 1250269
  have htrace : WordTrace (prefixWord ++ tailWord_1250269) baseStart_1250269 baseEnd_1250269 := by
    simpa [prefixWord, tailWord_1250269, baseEnd_1250269] using wordTrace_append hprefix tailTrace_1250269
  have hstable : (prefixWord ++ tailWord_1250269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250269).length < 2 ^ (prefixWord ++ tailWord_1250269).sum := by decide
  have hdescent : baseEnd_1250269 < baseStart_1250269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250297 : List Nat := [1, 2, 1, 3, 1, 3, 3, 2, 6]
def baseStart_1250297 : Nat := 118140960795 + 1250297 * 2 ^ 59
def prefixEnd_1250297 : Nat := 4983230072969 + 3 ^ 40 * 1250297 * 2
def baseEnd_1250297 : Nat := 142667404861022209097221

theorem tailTrace_1250297 : CollatzResearch.WordTrace tailWord_1250297 prefixEnd_1250297 142667404861022209097221 := by
  unfold tailWord_1250297
  simp only [CollatzResearch.WordTrace]
  refine ⟨45602077951394977572421145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30401385300929985048280763 45602077951394977572421145)
  ·
    refine ⟨34201558463546233179315859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45602077951394977572421145 34201558463546233179315859)
    ·
      refine ⟨51302337695319349768973789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34201558463546233179315859 51302337695319349768973789)
      ·
        refine ⟨19238376635744756163365171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51302337695319349768973789 19238376635744756163365171)
        ·
          refine ⟨28857564953617134245047757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19238376635744756163365171 28857564953617134245047757)
          ·
            refine ⟨10821586857606425341892909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28857564953617134245047757 10821586857606425341892909)
            ·
              refine ⟨4058095071602409503209841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10821586857606425341892909 4058095071602409503209841)
              ·
                refine ⟨3043571303701807127407381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4058095071602409503209841 3043571303701807127407381)
                ·
                  refine ⟨142667404861022209097221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3043571303701807127407381 142667404861022209097221)
                  ·
                    rfl

theorem cell22_1250297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 6].length) (baseStart_1250297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250297 prefixEnd_1250297 := by exact prefixLift 1250297
  have htrace : WordTrace (prefixWord ++ tailWord_1250297) baseStart_1250297 baseEnd_1250297 := by
    simpa [prefixWord, tailWord_1250297, baseEnd_1250297] using wordTrace_append hprefix tailTrace_1250297
  have hstable : (prefixWord ++ tailWord_1250297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250297).length < 2 ^ (prefixWord ++ tailWord_1250297).sum := by decide
  have hdescent : baseEnd_1250297 < baseStart_1250297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250316 : List Nat := [2, 2, 1, 2, 3, 2, 4, 1, 1, 4]
def baseStart_1250316 : Nat := 118140960795 + 1250316 * 2 ^ 59
def prefixEnd_1250316 : Nat := 4983230072969 + 3 ^ 40 * 1250316 * 2
def baseEnd_1250316 : Nat := 428008718671356911066605

theorem tailTrace_1250316 : CollatzResearch.WordTrace tailWord_1250316 prefixEnd_1250316 428008718671356911066605 := by
  unfold tailWord_1250316
  simp only [CollatzResearch.WordTrace]
  refine ⟨22801385469163071908681401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30401847292217429211575201 22801385469163071908681401)
  ·
    refine ⟨17101039101872303931511051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22801385469163071908681401 17101039101872303931511051)
    ·
      refine ⟨25651558652808455897266577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17101039101872303931511051 25651558652808455897266577)
      ·
        refine ⟨19238668989606341922949933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25651558652808455897266577 19238668989606341922949933)
        ·
          refine ⟨7214500871102378221106225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19238668989606341922949933 7214500871102378221106225)
          ·
            refine ⟨5410875653326783665829669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7214500871102378221106225 5410875653326783665829669)
            ·
              refine ⟨1014539184998771937343063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5410875653326783665829669 1014539184998771937343063)
              ·
                refine ⟨1521808777498157906014595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1014539184998771937343063 1521808777498157906014595)
                ·
                  refine ⟨2282713166247236859021893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1521808777498157906014595 2282713166247236859021893)
                  ·
                    refine ⟨428008718671356911066605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2282713166247236859021893 428008718671356911066605)
                    ·
                      rfl

theorem cell22_1250316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 1, 4].length) (baseStart_1250316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250316 prefixEnd_1250316 := by exact prefixLift 1250316
  have htrace : WordTrace (prefixWord ++ tailWord_1250316) baseStart_1250316 baseEnd_1250316 := by
    simpa [prefixWord, tailWord_1250316, baseEnd_1250316] using wordTrace_append hprefix tailTrace_1250316
  have hstable : (prefixWord ++ tailWord_1250316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250316).length < 2 ^ (prefixWord ++ tailWord_1250316).sum := by decide
  have hdescent : baseEnd_1250316 < baseStart_1250316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250357 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 1, 9]
def baseStart_1250357 : Nat := 118140960795 + 1250357 * 2 ^ 59
def prefixEnd_1250357 : Nat := 4983230072969 + 3 ^ 40 * 1250357 * 2
def baseEnd_1250357 : Nat := 428022753809246470791479

theorem tailTrace_1250357 : CollatzResearch.WordTrace tailWord_1250357 prefixEnd_1250357 428022753809246470791479 := by
  unfold tailWord_1250357
  simp only [CollatzResearch.WordTrace]
  refine ⟨45604266331177607819605325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30402844220785071879736883 45604266331177607819605325)
  ·
    refine ⟨17101599874191602932351997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45604266331177607819605325 17101599874191602932351997)
    ·
      refine ⟨6413099952821851099631999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17101599874191602932351997 6413099952821851099631999)
      ·
        refine ⟨9619649929232776649447999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6413099952821851099631999 9619649929232776649447999)
        ·
          refine ⟨14429474893849164974171999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9619649929232776649447999 14429474893849164974171999)
          ·
            refine ⟨21644212340773747461257999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14429474893849164974171999 21644212340773747461257999)
            ·
              refine ⟨32466318511160621191886999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21644212340773747461257999 32466318511160621191886999)
              ·
                refine ⟨48699477766740931787830499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32466318511160621191886999 48699477766740931787830499)
                ·
                  refine ⟨73049216650111397681745749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48699477766740931787830499 73049216650111397681745749)
                  ·
                    refine ⟨428022753809246470791479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 73049216650111397681745749 428022753809246470791479)
                    ·
                      rfl

theorem cell22_1250357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_1250357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250357 prefixEnd_1250357 := by exact prefixLift 1250357
  have htrace : WordTrace (prefixWord ++ tailWord_1250357) baseStart_1250357 baseEnd_1250357 := by
    simpa [prefixWord, tailWord_1250357, baseEnd_1250357] using wordTrace_append hprefix tailTrace_1250357
  have hstable : (prefixWord ++ tailWord_1250357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250357).length < 2 ^ (prefixWord ++ tailWord_1250357).sum := by decide
  have hdescent : baseEnd_1250357 < baseStart_1250357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250397 : List Nat := [1, 4, 4, 1, 2, 2, 2, 1, 2, 3]
def baseStart_1250397 : Nat := 118140960795 + 1250397 * 2 ^ 59
def prefixEnd_1250397 : Nat := 4983230072969 + 3 ^ 40 * 1250397 * 2
def baseEnd_1250397 : Nat := 428036446626699699791357

theorem tailTrace_1250397 : CollatzResearch.WordTrace tailWord_1250397 prefixEnd_1250397 428036446626699699791357 := by
  unfold tailWord_1250397
  simp only [CollatzResearch.WordTrace]
  refine ⟨45605725251032694651061445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30403816834021796434040963 45605725251032694651061445)
  ·
    refine ⟨8551073484568630247074021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45605725251032694651061445 8551073484568630247074021)
    ·
      refine ⟨1603326278356618171326379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8551073484568630247074021 1603326278356618171326379)
      ·
        refine ⟨2404989417534927256989569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1603326278356618171326379 2404989417534927256989569)
        ·
          refine ⟨1803742063151195442742177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2404989417534927256989569 1803742063151195442742177)
          ·
            refine ⟨1352806547363396582056633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1803742063151195442742177 1352806547363396582056633)
            ·
              refine ⟨1014604910522547436542475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1352806547363396582056633 1014604910522547436542475)
              ·
                refine ⟨1521907365783821154813713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1014604910522547436542475 1521907365783821154813713)
                ·
                  refine ⟨1141430524337865866110285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1521907365783821154813713 1141430524337865866110285)
                  ·
                    refine ⟨428036446626699699791357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1141430524337865866110285 428036446626699699791357)
                    ·
                      rfl

theorem cell22_1250397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_1250397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250397 prefixEnd_1250397 := by exact prefixLift 1250397
  have htrace : WordTrace (prefixWord ++ tailWord_1250397) baseStart_1250397 baseEnd_1250397 := by
    simpa [prefixWord, tailWord_1250397, baseEnd_1250397] using wordTrace_append hprefix tailTrace_1250397
  have hstable : (prefixWord ++ tailWord_1250397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250397).length < 2 ^ (prefixWord ++ tailWord_1250397).sum := by decide
  have hdescent : baseEnd_1250397 < baseStart_1250397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250481 : List Nat := [1, 2, 2, 5, 1, 1, 2, 2, 1, 5]
def baseStart_1250481 : Nat := 118140960795 + 1250481 * 2 ^ 59
def prefixEnd_1250481 : Nat := 4983230072969 + 3 ^ 40 * 1250481 * 2
def baseEnd_1250481 : Nat := 428065201543351480691099

theorem tailTrace_1250481 : CollatzResearch.WordTrace tailWord_1250481 prefixEnd_1250481 428065201543351480691099 := by
  unfold tailWord_1250481
  simp only [CollatzResearch.WordTrace]
  refine ⟨45608788982728376997119297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30405859321818917998079531 45608788982728376997119297)
  ·
    refine ⟨34206591737046282747839473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45608788982728376997119297 34206591737046282747839473)
    ·
      refine ⟨25654943802784712060879605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34206591737046282747839473 25654943802784712060879605)
      ·
        refine ⟨2405150981511066755707463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25654943802784712060879605 2405150981511066755707463)
        ·
          refine ⟨3607726472266600133561195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2405150981511066755707463 3607726472266600133561195)
          ·
            refine ⟨5411589708399900200341793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3607726472266600133561195 5411589708399900200341793)
            ·
              refine ⟨4058692281299925150256345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5411589708399900200341793 4058692281299925150256345)
              ·
                refine ⟨3044019210974943862692259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4058692281299925150256345 3044019210974943862692259)
                ·
                  refine ⟨4566028816462415794038389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3044019210974943862692259 4566028816462415794038389)
                  ·
                    refine ⟨428065201543351480691099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4566028816462415794038389 428065201543351480691099)
                    ·
                      rfl

theorem cell22_1250481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_1250481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250481 prefixEnd_1250481 := by exact prefixLift 1250481
  have htrace : WordTrace (prefixWord ++ tailWord_1250481) baseStart_1250481 baseEnd_1250481 := by
    simpa [prefixWord, tailWord_1250481, baseEnd_1250481] using wordTrace_append hprefix tailTrace_1250481
  have hstable : (prefixWord ++ tailWord_1250481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250481).length < 2 ^ (prefixWord ++ tailWord_1250481).sum := by decide
  have hdescent : baseEnd_1250481 < baseStart_1250481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250539 : List Nat := [1, 1, 1, 1, 2, 6, 1, 2, 7]
def baseStart_1250539 : Nat := 118140960795 + 1250539 * 2 ^ 59
def prefixEnd_1250539 : Nat := 4983230072969 + 3 ^ 40 * 1250539 * 2
def baseEnd_1250539 : Nat := 142695018709552887580307

theorem tailTrace_1250539 : CollatzResearch.WordTrace tailWord_1250539 prefixEnd_1250539 142695018709552887580307 := by
  unfold tailWord_1250539
  simp only [CollatzResearch.WordTrace]
  refine ⟨45610904416518252902730671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30407269611012168601820447 45610904416518252902730671)
  ·
    refine ⟨68416356624777379354096007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45610904416518252902730671 68416356624777379354096007)
    ·
      refine ⟨102624534937166069031144011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68416356624777379354096007 102624534937166069031144011)
      ·
        refine ⟨153936802405749103546716017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102624534937166069031144011 153936802405749103546716017)
        ·
          refine ⟨115452601804311827660037013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153936802405749103546716017 115452601804311827660037013)
          ·
            refine ⟨5411840709577116921564235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 115452601804311827660037013 5411840709577116921564235)
            ·
              refine ⟨8117761064365675382346353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5411840709577116921564235 8117761064365675382346353)
              ·
                refine ⟨6088320798274256536759765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8117761064365675382346353 6088320798274256536759765)
                ·
                  refine ⟨142695018709552887580307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6088320798274256536759765 142695018709552887580307)
                  ·
                    rfl

theorem cell22_1250539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 7].length) (baseStart_1250539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250539 prefixEnd_1250539 := by exact prefixLift 1250539
  have htrace : WordTrace (prefixWord ++ tailWord_1250539) baseStart_1250539 baseEnd_1250539 := by
    simpa [prefixWord, tailWord_1250539, baseEnd_1250539] using wordTrace_append hprefix tailTrace_1250539
  have hstable : (prefixWord ++ tailWord_1250539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250539).length < 2 ^ (prefixWord ++ tailWord_1250539).sum := by decide
  have hdescent : baseEnd_1250539 < baseStart_1250539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250618 : List Nat := [3, 1, 1, 1, 4, 1, 3, 4, 4]
def baseStart_1250618 : Nat := 118140960795 + 1250618 * 2 ^ 59
def prefixEnd_1250618 : Nat := 4983230072969 + 3 ^ 40 * 1250618 * 2
def baseEnd_1250618 : Nat := 142704033147709596671893

theorem tailTrace_1250618 : CollatzResearch.WordTrace tailWord_1250618 prefixEnd_1250618 142704033147709596671893 := by
  unfold tailWord_1250618
  simp only [CollatzResearch.WordTrace]
  refine ⟨11403446445808012348714127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30409190522154699596571005 11403446445808012348714127)
  ·
    refine ⟨17105169668712018523071191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11403446445808012348714127 17105169668712018523071191)
    ·
      refine ⟨25657754503068027784606787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17105169668712018523071191 25657754503068027784606787)
      ·
        refine ⟨38486631754602041676910181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25657754503068027784606787 38486631754602041676910181)
        ·
          refine ⟨7216243453987882814420659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38486631754602041676910181 7216243453987882814420659)
          ·
            refine ⟨10824365180981824221630989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7216243453987882814420659 10824365180981824221630989)
            ·
              refine ⟨4059136942868184083111621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10824365180981824221630989 4059136942868184083111621)
              ·
                refine ⟨761088176787784515583429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4059136942868184083111621 761088176787784515583429)
                ·
                  refine ⟨142704033147709596671893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 761088176787784515583429 142704033147709596671893)
                  ·
                    rfl

theorem cell22_1250618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 4, 4].length) (baseStart_1250618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250618 prefixEnd_1250618 := by exact prefixLift 1250618
  have htrace : WordTrace (prefixWord ++ tailWord_1250618) baseStart_1250618 baseEnd_1250618 := by
    simpa [prefixWord, tailWord_1250618, baseEnd_1250618] using wordTrace_append hprefix tailTrace_1250618
  have hstable : (prefixWord ++ tailWord_1250618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250618).length < 2 ^ (prefixWord ++ tailWord_1250618).sum := by decide
  have hdescent : baseEnd_1250618 < baseStart_1250618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250633 : List Nat := [1, 2, 1, 1, 2, 3, 4, 3, 2, 3]
def baseStart_1250633 : Nat := 118140960795 + 1250633 * 2 ^ 59
def prefixEnd_1250633 : Nat := 4983230072969 + 3 ^ 40 * 1250633 * 2
def baseEnd_1250633 : Nat := 428117234249673750890633

theorem tailTrace_1250633 : CollatzResearch.WordTrace tailWord_1250633 prefixEnd_1250633 428117234249673750890633 := by
  unfold tailWord_1250633
  simp only [CollatzResearch.WordTrace]
  refine ⟨45614332878177706956652553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30409555252118471304435035 45614332878177706956652553)
  ·
    refine ⟨34210749658633280217489415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45614332878177706956652553 34210749658633280217489415)
    ·
      refine ⟨51316124487949920326234123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34210749658633280217489415 51316124487949920326234123)
      ·
        refine ⟨76974186731924880489351185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51316124487949920326234123 76974186731924880489351185)
        ·
          refine ⟨57730640048943660367013389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76974186731924880489351185 57730640048943660367013389)
          ·
            refine ⟨21648990018353872637630021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57730640048943660367013389 21648990018353872637630021)
            ·
              refine ⟨4059185628441351119555629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21648990018353872637630021 4059185628441351119555629)
              ·
                refine ⟨1522194610665506669833361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4059185628441351119555629 1522194610665506669833361)
                ·
                  refine ⟨1141645957999130002375021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1522194610665506669833361 1141645957999130002375021)
                  ·
                    refine ⟨428117234249673750890633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1141645957999130002375021 428117234249673750890633)
                    ·
                      rfl

theorem cell22_1250633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 2, 3].length) (baseStart_1250633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250633 prefixEnd_1250633 := by exact prefixLift 1250633
  have htrace : WordTrace (prefixWord ++ tailWord_1250633) baseStart_1250633 baseEnd_1250633 := by
    simpa [prefixWord, tailWord_1250633, baseEnd_1250633] using wordTrace_append hprefix tailTrace_1250633
  have hstable : (prefixWord ++ tailWord_1250633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250633).length < 2 ^ (prefixWord ++ tailWord_1250633).sum := by decide
  have hdescent : baseEnd_1250633 < baseStart_1250633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250708 : List Nat := [2, 4, 2, 1, 2, 1, 1, 2, 7]
def baseStart_1250708 : Nat := 118140960795 + 1250708 * 2 ^ 59
def prefixEnd_1250708 : Nat := 4983230072969 + 3 ^ 40 * 1250708 * 2
def baseEnd_1250708 : Nat := 142714302760799518421801

theorem tailTrace_1250708 : CollatzResearch.WordTrace tailWord_1250708 prefixEnd_1250708 142714302760799518421801 := by
  unfold tailWord_1250708
  simp only [CollatzResearch.WordTrace]
  refine ⟨22808534176452997382816389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30411378901937329843755185 22808534176452997382816389)
  ·
    refine ⟨4276600158084937009278073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22808534176452997382816389 4276600158084937009278073)
    ·
      refine ⟨3207450118563702756958555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4276600158084937009278073 3207450118563702756958555)
      ·
        refine ⟨4811175177845554135437833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3207450118563702756958555 4811175177845554135437833)
        ·
          refine ⟨3608381383384165601578375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4811175177845554135437833 3608381383384165601578375)
          ·
            refine ⟨5412572075076248402367563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3608381383384165601578375 5412572075076248402367563)
            ·
              refine ⟨8118858112614372603551345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5412572075076248402367563 8118858112614372603551345)
              ·
                refine ⟨6089143584460779452663509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8118858112614372603551345 6089143584460779452663509)
                ·
                  refine ⟨142714302760799518421801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6089143584460779452663509 142714302760799518421801)
                  ·
                    rfl

theorem cell22_1250708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_1250708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250708 prefixEnd_1250708 := by exact prefixLift 1250708
  have htrace : WordTrace (prefixWord ++ tailWord_1250708) baseStart_1250708 baseEnd_1250708 := by
    simpa [prefixWord, tailWord_1250708, baseEnd_1250708] using wordTrace_append hprefix tailTrace_1250708
  have hstable : (prefixWord ++ tailWord_1250708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250708).length < 2 ^ (prefixWord ++ tailWord_1250708).sum := by decide
  have hdescent : baseEnd_1250708 < baseStart_1250708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250736 : List Nat := [2, 1, 1, 1, 2, 1, 1, 7, 6]
def baseStart_1250736 : Nat := 118140960795 + 1250736 * 2 ^ 59
def prefixEnd_1250736 : Nat := 4983230072969 + 3 ^ 40 * 1250736 * 2
def baseEnd_1250736 : Nat := 142717497751538605188439

theorem tailTrace_1250736 : CollatzResearch.WordTrace tailWord_1250736 prefixEnd_1250736 142717497751538605188439 := by
  unfold tailWord_1250736
  simp only [CollatzResearch.WordTrace]
  refine ⟨22809044798402277773826031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30412059731203037031768041 22809044798402277773826031)
  ·
    refine ⟨34213567197603416660739047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22809044798402277773826031 34213567197603416660739047)
    ·
      refine ⟨51320350796405124991108571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34213567197603416660739047 51320350796405124991108571)
      ·
        refine ⟨76980526194607687486662857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51320350796405124991108571 76980526194607687486662857)
        ·
          refine ⟨57735394645955765614997143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76980526194607687486662857 57735394645955765614997143)
          ·
            refine ⟨86603091968933648422495715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57735394645955765614997143 86603091968933648422495715)
            ·
              refine ⟨129904637953400472633743573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86603091968933648422495715 129904637953400472633743573)
              ·
                refine ⟨3044639952032823577353365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 129904637953400472633743573 3044639952032823577353365)
                ·
                  refine ⟨142717497751538605188439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3044639952032823577353365 142717497751538605188439)
                  ·
                    rfl

theorem cell22_1250736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 6].length) (baseStart_1250736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250736 prefixEnd_1250736 := by exact prefixLift 1250736
  have htrace : WordTrace (prefixWord ++ tailWord_1250736) baseStart_1250736 baseEnd_1250736 := by
    simpa [prefixWord, tailWord_1250736, baseEnd_1250736] using wordTrace_append hprefix tailTrace_1250736
  have hstable : (prefixWord ++ tailWord_1250736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250736).length < 2 ^ (prefixWord ++ tailWord_1250736).sum := by decide
  have hdescent : baseEnd_1250736 < baseStart_1250736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250751 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 5, 5]
def baseStart_1250751 : Nat := 118140960795 + 1250751 * 2 ^ 59
def prefixEnd_1250751 : Nat := 4983230072969 + 3 ^ 40 * 1250751 * 2
def baseEnd_1250751 : Nat := 428157628061160776440271

theorem tailTrace_1250751 : CollatzResearch.WordTrace tailWord_1250751 prefixEnd_1250751 428157628061160776440271 := by
  unfold tailWord_1250751
  simp only [CollatzResearch.WordTrace]
  refine ⟨45618636691750213109448107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30412424461166808739632071 45618636691750213109448107)
  ·
    refine ⟨68427955037625319664172161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45618636691750213109448107 68427955037625319664172161)
    ·
      refine ⟨51320966278218989748129121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68427955037625319664172161 51320966278218989748129121)
      ·
        refine ⟨38490724708664242311096841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51320966278218989748129121 38490724708664242311096841)
        ·
          refine ⟨28868043531498181733322631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38490724708664242311096841 28868043531498181733322631)
          ·
            refine ⟨43302065297247272599983947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28868043531498181733322631 43302065297247272599983947)
            ·
              refine ⟨64953097945870908899975921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43302065297247272599983947 64953097945870908899975921)
              ·
                refine ⟨48714823459403181674981941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64953097945870908899975921 48714823459403181674981941)
                ·
                  refine ⟨4567014699319048282029557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48714823459403181674981941 4567014699319048282029557)
                  ·
                    refine ⟨428157628061160776440271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4567014699319048282029557 428157628061160776440271)
                    ·
                      rfl

theorem cell22_1250751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 5].length) (baseStart_1250751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250751 prefixEnd_1250751 := by exact prefixLift 1250751
  have htrace : WordTrace (prefixWord ++ tailWord_1250751) baseStart_1250751 baseEnd_1250751 := by
    simpa [prefixWord, tailWord_1250751, baseEnd_1250751] using wordTrace_append hprefix tailTrace_1250751
  have hstable : (prefixWord ++ tailWord_1250751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250751).length < 2 ^ (prefixWord ++ tailWord_1250751).sum := by decide
  have hdescent : baseEnd_1250751 < baseStart_1250751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250783 : List Nat := [1, 1, 2, 3, 3, 1, 1, 4, 2, 4]
def baseStart_1250783 : Nat := 118140960795 + 1250783 * 2 ^ 59
def prefixEnd_1250783 : Nat := 4983230072969 + 3 ^ 40 * 1250783 * 2
def baseEnd_1250783 : Nat := 428168582315123359640173

theorem tailTrace_1250783 : CollatzResearch.WordTrace tailWord_1250783 prefixEnd_1250783 428168582315123359640173 := by
  unfold tailWord_1250783
  simp only [CollatzResearch.WordTrace]
  refine ⟨45619803827634282574613003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30413202551756188383075335 45619803827634282574613003)
  ·
    refine ⟨68429705741451423861919505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45619803827634282574613003 68429705741451423861919505)
    ·
      refine ⟨51322279306088567896439629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68429705741451423861919505 51322279306088567896439629)
      ·
        refine ⟨19245854739783212961164861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51322279306088567896439629 19245854739783212961164861)
        ·
          refine ⟨7217195527418704860436823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19245854739783212961164861 7217195527418704860436823)
          ·
            refine ⟨10825793291128057290655235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7217195527418704860436823 10825793291128057290655235)
            ·
              refine ⟨16238689936692085935982853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10825793291128057290655235 16238689936692085935982853)
              ·
                refine ⟨3044754363129766112996785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16238689936692085935982853 3044754363129766112996785)
                ·
                  refine ⟨2283565772347324584747589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3044754363129766112996785 2283565772347324584747589)
                  ·
                    refine ⟨428168582315123359640173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2283565772347324584747589 428168582315123359640173)
                    ·
                      rfl

theorem cell22_1250783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 4].length) (baseStart_1250783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250783 prefixEnd_1250783 := by exact prefixLift 1250783
  have htrace : WordTrace (prefixWord ++ tailWord_1250783) baseStart_1250783 baseEnd_1250783 := by
    simpa [prefixWord, tailWord_1250783, baseEnd_1250783] using wordTrace_append hprefix tailTrace_1250783
  have hstable : (prefixWord ++ tailWord_1250783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250783).length < 2 ^ (prefixWord ++ tailWord_1250783).sum := by decide
  have hdescent : baseEnd_1250783 < baseStart_1250783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250785 : List Nat := [1, 2, 3, 1, 2, 3, 1, 4, 2, 3]
def baseStart_1250785 : Nat := 118140960795 + 1250785 * 2 ^ 59
def prefixEnd_1250785 : Nat := 4983230072969 + 3 ^ 40 * 1250785 * 2
def baseEnd_1250785 : Nat := 428169266955996021090167

theorem tailTrace_1250785 : CollatzResearch.WordTrace tailWord_1250785 prefixEnd_1250785 428169266955996021090167 := by
  unfold tailWord_1250785
  simp only [CollatzResearch.WordTrace]
  refine ⟨45619876773627036916185809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30413251182418024610790539 45619876773627036916185809)
  ·
    refine ⟨34214907580220277687139357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45619876773627036916185809 34214907580220277687139357)
    ·
      refine ⟨12830590342582604132677259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34214907580220277687139357 12830590342582604132677259)
      ·
        refine ⟨19245885513873906199015889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12830590342582604132677259 19245885513873906199015889)
        ·
          refine ⟨14434414135405429649261917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19245885513873906199015889 14434414135405429649261917)
          ·
            refine ⟨5412905300777036118473219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14434414135405429649261917 5412905300777036118473219)
            ·
              refine ⟨8119357951165554177709829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5412905300777036118473219 8119357951165554177709829)
              ·
                refine ⟨1522379615843541408320593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8119357951165554177709829 1522379615843541408320593)
                ·
                  refine ⟨1141784711882656056240445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1522379615843541408320593 1141784711882656056240445)
                  ·
                    refine ⟨428169266955996021090167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1141784711882656056240445 428169266955996021090167)
                    ·
                      rfl

theorem cell22_1250785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_1250785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250785 prefixEnd_1250785 := by exact prefixLift 1250785
  have htrace : WordTrace (prefixWord ++ tailWord_1250785) baseStart_1250785 baseEnd_1250785 := by
    simpa [prefixWord, tailWord_1250785, baseEnd_1250785] using wordTrace_append hprefix tailTrace_1250785
  have hstable : (prefixWord ++ tailWord_1250785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250785).length < 2 ^ (prefixWord ++ tailWord_1250785).sum := by decide
  have hdescent : baseEnd_1250785 < baseStart_1250785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250787 : List Nat := [1, 1, 1, 6, 2, 1, 4, 2, 4]
def baseStart_1250787 : Nat := 118140960795 + 1250787 * 2 ^ 59
def prefixEnd_1250787 : Nat := 4983230072969 + 3 ^ 40 * 1250787 * 2
def baseEnd_1250787 : Nat := 142723317198956227513387

theorem tailTrace_1250787 : CollatzResearch.WordTrace tailWord_1250787 prefixEnd_1250787 142723317198956227513387 := by
  unfold tailWord_1250787
  simp only [CollatzResearch.WordTrace]
  refine ⟨45619949719619791257758615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30413299813079860838505743 45619949719619791257758615)
  ·
    refine ⟨68429924579429686886637923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45619949719619791257758615 68429924579429686886637923)
    ·
      refine ⟨102644886869144530329956885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68429924579429686886637923 102644886869144530329956885)
      ·
        refine ⟨4811479071991149859216729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 102644886869144530329956885 4811479071991149859216729)
        ·
          refine ⟨3608609303993362394412547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4811479071991149859216729 3608609303993362394412547)
          ·
            refine ⟨5412913955990043591618821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3608609303993362394412547 5412913955990043591618821)
            ·
              refine ⟨1014921366748133173428529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5412913955990043591618821 1014921366748133173428529)
              ·
                refine ⟨761191025061099880071397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1014921366748133173428529 761191025061099880071397)
                ·
                  refine ⟨142723317198956227513387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 761191025061099880071397 142723317198956227513387)
                  ·
                    rfl

theorem cell22_1250787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 2, 4].length) (baseStart_1250787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250787 prefixEnd_1250787 := by exact prefixLift 1250787
  have htrace : WordTrace (prefixWord ++ tailWord_1250787) baseStart_1250787 baseEnd_1250787 := by
    simpa [prefixWord, tailWord_1250787, baseEnd_1250787] using wordTrace_append hprefix tailTrace_1250787
  have hstable : (prefixWord ++ tailWord_1250787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250787).length < 2 ^ (prefixWord ++ tailWord_1250787).sum := by decide
  have hdescent : baseEnd_1250787 < baseStart_1250787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250802 : List Nat := [3, 2, 1, 4, 1, 1, 2, 3, 2, 3]
def baseStart_1250802 : Nat := 118140960795 + 1250802 * 2 ^ 59
def prefixEnd_1250802 : Nat := 4983230072969 + 3 ^ 40 * 1250802 * 2
def baseEnd_1250802 : Nat := 428175086403413643415115

theorem tailTrace_1250802 : CollatzResearch.WordTrace tailWord_1250802 prefixEnd_1250802 428175086403413643415115 := by
  unfold tailWord_1250802
  simp only [CollatzResearch.WordTrace]
  refine ⟨11405124203641362204888665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30413664543043632546369773 11405124203641362204888665)
  ·
    refine ⟨8553843152731021653666499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11405124203641362204888665 8553843152731021653666499)
    ·
      refine ⟨12830764729096532480499749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8553843152731021653666499 12830764729096532480499749)
      ·
        refine ⟨2405768386705599840093703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12830764729096532480499749 2405768386705599840093703)
        ·
          refine ⟨3608652580058399760140555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2405768386705599840093703 3608652580058399760140555)
          ·
            refine ⟨5412978870087599640210833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3608652580058399760140555 5412978870087599640210833)
            ·
              refine ⟨4059734152565699730158125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5412978870087599640210833 4059734152565699730158125)
              ·
                refine ⟨1522400307212137398809297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4059734152565699730158125 1522400307212137398809297)
                ·
                  refine ⟨1141800230409103049106973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1522400307212137398809297 1141800230409103049106973)
                  ·
                    refine ⟨428175086403413643415115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1141800230409103049106973 428175086403413643415115)
                    ·
                      rfl

theorem cell22_1250802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_1250802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250802 prefixEnd_1250802 := by exact prefixLift 1250802
  have htrace : WordTrace (prefixWord ++ tailWord_1250802) baseStart_1250802 baseEnd_1250802 := by
    simpa [prefixWord, tailWord_1250802, baseEnd_1250802] using wordTrace_append hprefix tailTrace_1250802
  have hstable : (prefixWord ++ tailWord_1250802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250802).length < 2 ^ (prefixWord ++ tailWord_1250802).sum := by decide
  have hdescent : baseEnd_1250802 < baseStart_1250802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250817 : List Nat := [1, 2, 4, 1, 4, 2, 1, 1, 2, 4]
def baseStart_1250817 : Nat := 118140960795 + 1250817 * 2 ^ 59
def prefixEnd_1250817 : Nat := 4983230072969 + 3 ^ 40 * 1250817 * 2
def baseEnd_1250817 : Nat := 428180221209958604290069

theorem tailTrace_1250817 : CollatzResearch.WordTrace tailWord_1250817 prefixEnd_1250817 428180221209958604290069 := by
  unfold tailWord_1250817
  simp only [CollatzResearch.WordTrace]
  refine ⟨45621043909511106381350705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30414029273007404254233803 45621043909511106381350705)
  ·
    refine ⟨34215782932133329786013029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45621043909511106381350705 34215782932133329786013029)
    ·
      refine ⟨6415459299774999334877443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34215782932133329786013029 6415459299774999334877443)
      ·
        refine ⟨9623188949662499002316165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6415459299774999334877443 9623188949662499002316165)
        ·
          refine ⟨1804347928061718562934281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9623188949662499002316165 1804347928061718562934281)
          ·
            refine ⟨1353260946046288922200711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1804347928061718562934281 1353260946046288922200711)
            ·
              refine ⟨2029891419069433383301067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1353260946046288922200711 2029891419069433383301067)
              ·
                refine ⟨3044837128604150074951601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2029891419069433383301067 3044837128604150074951601)
                ·
                  refine ⟨2283627846453112556213701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3044837128604150074951601 2283627846453112556213701)
                  ·
                    refine ⟨428180221209958604290069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2283627846453112556213701 428180221209958604290069)
                    ·
                      rfl

theorem cell22_1250817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_1250817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250817 prefixEnd_1250817 := by exact prefixLift 1250817
  have htrace : WordTrace (prefixWord ++ tailWord_1250817) baseStart_1250817 baseEnd_1250817 := by
    simpa [prefixWord, tailWord_1250817, baseEnd_1250817] using wordTrace_append hprefix tailTrace_1250817
  have hstable : (prefixWord ++ tailWord_1250817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250817).length < 2 ^ (prefixWord ++ tailWord_1250817).sum := by decide
  have hdescent : baseEnd_1250817 < baseStart_1250817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250836 : List Nat := [2, 4, 3, 1, 2, 2, 1, 2, 2, 3]
def baseStart_1250836 : Nat := 118140960795 + 1250836 * 2 ^ 59
def prefixEnd_1250836 : Nat := 4983230072969 + 3 ^ 40 * 1250836 * 2
def baseEnd_1250836 : Nat := 428186725298248888065011

theorem tailTrace_1250836 : CollatzResearch.WordTrace tailWord_1250836 prefixEnd_1250836 428186725298248888065011 := by
  unfold tailWord_1250836
  simp only [CollatzResearch.WordTrace]
  refine ⟨22810868448221136313146181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30414491264294848417528241 22810868448221136313146181)
  ·
    refine ⟨4277037834041463058714909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22810868448221136313146181 4277037834041463058714909)
    ·
      refine ⟨1603889187765548647018091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4277037834041463058714909 1603889187765548647018091)
      ·
        refine ⟨2405833781648322970527137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1603889187765548647018091 2405833781648322970527137)
        ·
          refine ⟨1804375336236242227895353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2405833781648322970527137 1804375336236242227895353)
          ·
            refine ⟨1353281502177181670921515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1804375336236242227895353 1353281502177181670921515)
            ·
              refine ⟨2029922253265772506382273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1353281502177181670921515 2029922253265772506382273)
              ·
                refine ⟨1522441689949329379786705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2029922253265772506382273 1522441689949329379786705)
                ·
                  refine ⟨1141831267461997034840029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1522441689949329379786705 1141831267461997034840029)
                  ·
                    refine ⟨428186725298248888065011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1141831267461997034840029 428186725298248888065011)
                    ·
                      rfl

theorem cell22_1250836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_1250836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250836 prefixEnd_1250836 := by exact prefixLift 1250836
  have htrace : WordTrace (prefixWord ++ tailWord_1250836) baseStart_1250836 baseEnd_1250836 := by
    simpa [prefixWord, tailWord_1250836, baseEnd_1250836] using wordTrace_append hprefix tailTrace_1250836
  have hstable : (prefixWord ++ tailWord_1250836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250836).length < 2 ^ (prefixWord ++ tailWord_1250836).sum := by decide
  have hdescent : baseEnd_1250836 < baseStart_1250836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250847 : List Nat := [1, 1, 2, 4, 1, 1, 4, 4, 1, 3]
def baseStart_1250847 : Nat := 118140960795 + 1250847 * 2 ^ 59
def prefixEnd_1250847 : Nat := 4983230072969 + 3 ^ 40 * 1250847 * 2
def baseEnd_1250847 : Nat := 428190490823048526039977

theorem tailTrace_1250847 : CollatzResearch.WordTrace tailWord_1250847 prefixEnd_1250847 428190490823048526039977 := by
  unfold tailWord_1250847
  simp only [CollatzResearch.WordTrace]
  refine ⟨45622138099402421504942795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30414758732934947669961863 45622138099402421504942795)
  ·
    refine ⟨68433207149103632257414193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45622138099402421504942795 68433207149103632257414193)
    ·
      refine ⟨51324905361827724193060645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68433207149103632257414193 51324905361827724193060645)
      ·
        refine ⟨9623419755342698286198871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51324905361827724193060645 9623419755342698286198871)
        ·
          refine ⟨14435129633014047429298307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9623419755342698286198871 14435129633014047429298307)
          ·
            refine ⟨21652694449521071143947461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14435129633014047429298307 21652694449521071143947461)
            ·
              refine ⟨4059880209285200839490149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21652694449521071143947461 4059880209285200839490149)
              ·
                refine ⟨761227539240975157404403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4059880209285200839490149 761227539240975157404403)
                ·
                  refine ⟨1141841308861462736106605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 761227539240975157404403 1141841308861462736106605)
                  ·
                    refine ⟨428190490823048526039977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1141841308861462736106605 428190490823048526039977)
                    ·
                      rfl

theorem cell22_1250847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 4, 1, 3].length) (baseStart_1250847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250847 prefixEnd_1250847 := by exact prefixLift 1250847
  have htrace : WordTrace (prefixWord ++ tailWord_1250847) baseStart_1250847 baseEnd_1250847 := by
    simpa [prefixWord, tailWord_1250847, baseEnd_1250847] using wordTrace_append hprefix tailTrace_1250847
  have hstable : (prefixWord ++ tailWord_1250847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250847).length < 2 ^ (prefixWord ++ tailWord_1250847).sum := by decide
  have hdescent : baseEnd_1250847 < baseStart_1250847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250890 : List Nat := [3, 1, 2, 1, 1, 3, 1, 5, 1, 4]
def baseStart_1250890 : Nat := 118140960795 + 1250890 * 2 ^ 59
def prefixEnd_1250890 : Nat := 4983230072969 + 3 ^ 40 * 1250890 * 2
def baseEnd_1250890 : Nat := 428205210601810747214845

theorem tailTrace_1250890 : CollatzResearch.WordTrace tailWord_1250890 prefixEnd_1250890 428205210601810747214845 := by
  unfold tailWord_1250890
  simp only [CollatzResearch.WordTrace]
  refine ⟨11405926609561659962189531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30415804292164426565838749 11405926609561659962189531)
  ·
    refine ⟨17108889914342489943284297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11405926609561659962189531 17108889914342489943284297)
    ·
      refine ⟨12831667435756867457463223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17108889914342489943284297 12831667435756867457463223)
      ·
        refine ⟨19247501153635301186194835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12831667435756867457463223 19247501153635301186194835)
        ·
          refine ⟨28871251730452951779292253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19247501153635301186194835 28871251730452951779292253)
          ·
            refine ⟨10826719398919856917234595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28871251730452951779292253 10826719398919856917234595)
            ·
              refine ⟨16240079098379785375851893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10826719398919856917234595 16240079098379785375851893)
              ·
                refine ⟨1522507415473104878986115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16240079098379785375851893 1522507415473104878986115)
                ·
                  refine ⟨2283761123209657318479173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1522507415473104878986115 2283761123209657318479173)
                  ·
                    refine ⟨428205210601810747214845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2283761123209657318479173 428205210601810747214845)
                    ·
                      rfl

theorem cell22_1250890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_1250890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250890 prefixEnd_1250890 := by exact prefixLift 1250890
  have htrace : WordTrace (prefixWord ++ tailWord_1250890) baseStart_1250890 baseEnd_1250890 := by
    simpa [prefixWord, tailWord_1250890, baseEnd_1250890] using wordTrace_append hprefix tailTrace_1250890
  have hstable : (prefixWord ++ tailWord_1250890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250890).length < 2 ^ (prefixWord ++ tailWord_1250890).sum := by decide
  have hdescent : baseEnd_1250890 < baseStart_1250890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250905 : List Nat := [1, 2, 1, 2, 2, 1, 1, 8, 4]
def baseStart_1250905 : Nat := 118140960795 + 1250905 * 2 ^ 59
def prefixEnd_1250905 : Nat := 4983230072969 + 3 ^ 40 * 1250905 * 2
def baseEnd_1250905 : Nat := 142736781802785236029933

theorem tailTrace_1250905 : CollatzResearch.WordTrace tailWord_1250905 prefixEnd_1250905 142736781802785236029933 := by
  unfold tailWord_1250905
  simp only [CollatzResearch.WordTrace]
  refine ⟨45624253533192297410554169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30416169022128198273702779 45624253533192297410554169)
  ·
    refine ⟨34218190149894223057915627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45624253533192297410554169 34218190149894223057915627)
    ·
      refine ⟨51327285224841334586873441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34218190149894223057915627 51327285224841334586873441)
      ·
        refine ⟨38495463918631000940155081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51327285224841334586873441 38495463918631000940155081)
        ·
          refine ⟨28871597938973250705116311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38495463918631000940155081 28871597938973250705116311)
          ·
            refine ⟨43307396908459876057674467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28871597938973250705116311 43307396908459876057674467)
            ·
              refine ⟨64961095362689814086511701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43307396908459876057674467 64961095362689814086511701)
              ·
                refine ⟨761262836281521258826309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 64961095362689814086511701 761262836281521258826309)
                ·
                  refine ⟨142736781802785236029933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 761262836281521258826309 142736781802785236029933)
                  ·
                    rfl

theorem cell22_1250905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 8, 4].length) (baseStart_1250905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250905 prefixEnd_1250905 := by exact prefixLift 1250905
  have htrace : WordTrace (prefixWord ++ tailWord_1250905) baseStart_1250905 baseEnd_1250905 := by
    simpa [prefixWord, tailWord_1250905, baseEnd_1250905] using wordTrace_append hprefix tailTrace_1250905
  have hstable : (prefixWord ++ tailWord_1250905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250905).length < 2 ^ (prefixWord ++ tailWord_1250905).sum := by decide
  have hdescent : baseEnd_1250905 < baseStart_1250905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250954 : List Nat := [3, 1, 2, 3, 2, 2, 2, 2, 2, 3]
def baseStart_1250954 : Nat := 118140960795 + 1250954 * 2 ^ 59
def prefixEnd_1250954 : Nat := 4983230072969 + 3 ^ 40 * 1250954 * 2
def baseEnd_1250954 : Nat := 428227119109735913614649

theorem tailTrace_1250954 : CollatzResearch.WordTrace tailWord_1250954 prefixEnd_1250954 428227119109735913614649 := by
  unfold tailWord_1250954
  simp only [CollatzResearch.WordTrace]
  refine ⟨11406510177503694694771979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30417360473343185852725277 11406510177503694694771979)
  ·
    refine ⟨17109765266255542042157969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11406510177503694694771979 17109765266255542042157969)
    ·
      refine ⟨12832323949691656531618477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17109765266255542042157969 12832323949691656531618477)
      ·
        refine ⟨4812121481134371199356929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12832323949691656531618477 4812121481134371199356929)
        ·
          refine ⟨3609091110850778399517697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4812121481134371199356929 3609091110850778399517697)
          ·
            refine ⟨2706818333138083799638273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3609091110850778399517697 2706818333138083799638273)
            ·
              refine ⟨2030113749853562849728705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2706818333138083799638273 2030113749853562849728705)
              ·
                refine ⟨1522585312390172137296529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2030113749853562849728705 1522585312390172137296529)
                ·
                  refine ⟨1141938984292629102972397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1522585312390172137296529 1141938984292629102972397)
                  ·
                    refine ⟨428227119109735913614649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1141938984292629102972397 428227119109735913614649)
                    ·
                      rfl

theorem cell22_1250954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_1250954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250954 prefixEnd_1250954 := by exact prefixLift 1250954
  have htrace : WordTrace (prefixWord ++ tailWord_1250954) baseStart_1250954 baseEnd_1250954 := by
    simpa [prefixWord, tailWord_1250954, baseEnd_1250954] using wordTrace_append hprefix tailTrace_1250954
  have hstable : (prefixWord ++ tailWord_1250954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250954).length < 2 ^ (prefixWord ++ tailWord_1250954).sum := by decide
  have hdescent : baseEnd_1250954 < baseStart_1250954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250965 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 7, 3]
def baseStart_1250965 : Nat := 118140960795 + 1250965 * 2 ^ 59
def prefixEnd_1250965 : Nat := 4983230072969 + 3 ^ 40 * 1250965 * 2
def baseEnd_1250965 : Nat := 428230884634535551589615

theorem tailTrace_1250965 : CollatzResearch.WordTrace tailWord_1250965 prefixEnd_1250965 428230884634535551589615 := by
  unfold tailWord_1250965
  simp only [CollatzResearch.WordTrace]
  refine ⟨45626441912974927657738349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30417627941983285105158899 45626441912974927657738349)
  ·
    refine ⟨17109915717365597871651881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45626441912974927657738349 17109915717365597871651881)
    ·
      refine ⟨12832436788024198403738911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17109915717365597871651881 12832436788024198403738911)
      ·
        refine ⟨19248655182036297605608367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12832436788024198403738911 19248655182036297605608367)
        ·
          refine ⟨28872982773054446408412551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19248655182036297605608367 28872982773054446408412551)
          ·
            refine ⟨43309474159581669612618827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28872982773054446408412551 43309474159581669612618827)
            ·
              refine ⟨64964211239372504418928241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43309474159581669612618827 64964211239372504418928241)
              ·
                refine ⟨48723158429529378314196181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64964211239372504418928241 48723158429529378314196181)
                ·
                  refine ⟨1141949025692094804238973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 48723158429529378314196181 1141949025692094804238973)
                  ·
                    refine ⟨428230884634535551589615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1141949025692094804238973 428230884634535551589615)
                    ·
                      rfl

theorem cell22_1250965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_1250965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250965 prefixEnd_1250965 := by exact prefixLift 1250965
  have htrace : WordTrace (prefixWord ++ tailWord_1250965) baseStart_1250965 baseEnd_1250965 := by
    simpa [prefixWord, tailWord_1250965, baseEnd_1250965] using wordTrace_append hprefix tailTrace_1250965
  have hstable : (prefixWord ++ tailWord_1250965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250965).length < 2 ^ (prefixWord ++ tailWord_1250965).sum := by decide
  have hdescent : baseEnd_1250965 < baseStart_1250965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250999 : List Nat := [1, 1, 3, 1, 5, 1, 1, 5, 1, 3]
def baseStart_1250999 : Nat := 118140960795 + 1250999 * 2 ^ 59
def prefixEnd_1250999 : Nat := 4983230072969 + 3 ^ 40 * 1250999 * 2
def baseEnd_1250999 : Nat := 428242523529370796239511

theorem tailTrace_1250999 : CollatzResearch.WordTrace tailWord_1250999 prefixEnd_1250999 428242523529370796239511 := by
  unfold tailWord_1250999
  simp only [CollatzResearch.WordTrace]
  refine ⟨45627681994851751464476051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30418454663234500976317367 45627681994851751464476051)
  ·
    refine ⟨68441522992277627196714077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45627681994851751464476051 68441522992277627196714077)
    ·
      refine ⟨25665571122104110198767779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68441522992277627196714077 25665571122104110198767779)
      ·
        refine ⟨38498356683156165298151669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25665571122104110198767779 38498356683156165298151669)
        ·
          refine ⟨3609220939045890496701719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38498356683156165298151669 3609220939045890496701719)
          ·
            refine ⟨5413831408568835745052579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3609220939045890496701719 5413831408568835745052579)
            ·
              refine ⟨8120747112853253617578869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5413831408568835745052579 8120747112853253617578869)
              ·
                refine ⟨761320041829992526648019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8120747112853253617578869 761320041829992526648019)
                ·
                  refine ⟨1141980062744988789972029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 761320041829992526648019 1141980062744988789972029)
                  ·
                    refine ⟨428242523529370796239511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1141980062744988789972029 428242523529370796239511)
                    ·
                      rfl

theorem cell22_1250999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 5, 1, 3].length) (baseStart_1250999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1250999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1250999 prefixEnd_1250999 := by exact prefixLift 1250999
  have htrace : WordTrace (prefixWord ++ tailWord_1250999) baseStart_1250999 baseEnd_1250999 := by
    simpa [prefixWord, tailWord_1250999, baseEnd_1250999] using wordTrace_append hprefix tailTrace_1250999
  have hstable : (prefixWord ++ tailWord_1250999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250999).length < 2 ^ (prefixWord ++ tailWord_1250999).sum := by decide
  have hdescent : baseEnd_1250999 < baseStart_1250999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251040 : List Nat := [2, 1, 1, 3, 1, 2, 4, 2, 6]
def baseStart_1251040 : Nat := 118140960795 + 1251040 * 2 ^ 59
def prefixEnd_1251040 : Nat := 4983230072969 + 3 ^ 40 * 1251040 * 2
def baseEnd_1251040 : Nat := 142752186222420118654795

theorem tailTrace_1251040 : CollatzResearch.WordTrace tailWord_1251040 prefixEnd_1251040 142752186222420118654795 := by
  unfold tailWord_1251040
  simp only [CollatzResearch.WordTrace]
  refine ⟨22814588693851607733359287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30419451591802143644479049 22814588693851607733359287)
  ·
    refine ⟨34221883040777411600038931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22814588693851607733359287 34221883040777411600038931)
    ·
      refine ⟨51332824561166117400058397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34221883040777411600038931 51332824561166117400058397)
      ·
        refine ⟨19249809210437294025021899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51332824561166117400058397 19249809210437294025021899)
        ·
          refine ⟨28874713815655941037532849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19249809210437294025021899 28874713815655941037532849)
          ·
            refine ⟨21656035361741955778149637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28874713815655941037532849 21656035361741955778149637)
            ·
              refine ⟨4060506630326616708403057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21656035361741955778149637 4060506630326616708403057)
              ·
                refine ⟨3045379972744962531302293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4060506630326616708403057 3045379972744962531302293)
                ·
                  refine ⟨142752186222420118654795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3045379972744962531302293 142752186222420118654795)
                  ·
                    rfl

theorem cell22_1251040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 6].length) (baseStart_1251040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1251040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1251040 prefixEnd_1251040 := by exact prefixLift 1251040
  have htrace : WordTrace (prefixWord ++ tailWord_1251040) baseStart_1251040 baseEnd_1251040 := by
    simpa [prefixWord, tailWord_1251040, baseEnd_1251040] using wordTrace_append hprefix tailTrace_1251040
  have hstable : (prefixWord ++ tailWord_1251040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251040).length < 2 ^ (prefixWord ++ tailWord_1251040).sum := by decide
  have hdescent : baseEnd_1251040 < baseStart_1251040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251055 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 3, 5]
def baseStart_1251055 : Nat := 118140960795 + 1251055 * 2 ^ 59
def prefixEnd_1251055 : Nat := 4983230072969 + 3 ^ 40 * 1251055 * 2
def baseEnd_1251055 : Nat := 428261693473805316839339

theorem tailTrace_1251055 : CollatzResearch.WordTrace tailWord_1251055 prefixEnd_1251055 428261693473805316839339 := by
  unfold tailWord_1251055
  simp only [CollatzResearch.WordTrace]
  refine ⟨45629724482648873028514619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30419816321765915352343079 45629724482648873028514619)
  ·
    refine ⟨68444586723973309542771929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45629724482648873028514619 68444586723973309542771929)
    ·
      refine ⟨51333440042979982157078947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68444586723973309542771929 51333440042979982157078947)
      ·
        refine ⟨77000160064469973235618421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51333440042979982157078947 77000160064469973235618421)
        ·
          refine ⟨7218765006044059990839227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77000160064469973235618421 7218765006044059990839227)
          ·
            refine ⟨10828147509066089986258841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7218765006044059990839227 10828147509066089986258841)
            ·
              refine ⟨8121110631799567489694131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10828147509066089986258841 8121110631799567489694131)
              ·
                refine ⟨12181665947699351234541197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8121110631799567489694131 12181665947699351234541197)
                ·
                  refine ⟨4568124730387256712952949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12181665947699351234541197 4568124730387256712952949)
                  ·
                    refine ⟨428261693473805316839339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4568124730387256712952949 428261693473805316839339)
                    ·
                      rfl

theorem cell22_1251055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 5].length) (baseStart_1251055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1251055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1251055 prefixEnd_1251055 := by exact prefixLift 1251055
  have htrace : WordTrace (prefixWord ++ tailWord_1251055) baseStart_1251055 baseEnd_1251055 := by
    simpa [prefixWord, tailWord_1251055, baseEnd_1251055] using wordTrace_append hprefix tailTrace_1251055
  have hstable : (prefixWord ++ tailWord_1251055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251055).length < 2 ^ (prefixWord ++ tailWord_1251055).sum := by decide
  have hdescent : baseEnd_1251055 < baseStart_1251055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251198 : List Nat := [4, 2, 3, 1, 1, 2, 3, 1, 5]
def baseStart_1251198 : Nat := 118140960795 + 1251198 * 2 ^ 59
def prefixEnd_1251198 : Nat := 4983230072969 + 3 ^ 40 * 1251198 * 2
def baseEnd_1251198 : Nat := 142770215098733536837967

theorem tailTrace_1251198 : CollatzResearch.WordTrace tailWord_1251198 prefixEnd_1251198 142770215098733536837967 := by
  unfold tailWord_1251198
  simp only [CollatzResearch.WordTrace]
  refine ⟨5704367515141351056371281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30423293414087205633980165 5704367515141351056371281)
  ·
    refine ⟨4278275636356013292278461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5704367515141351056371281 4278275636356013292278461)
    ·
      refine ⟨1604353363633504984604423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4278275636356013292278461 1604353363633504984604423)
      ·
        refine ⟨2406530045450257476906635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1604353363633504984604423 2406530045450257476906635)
        ·
          refine ⟨3609795068175386215359953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2406530045450257476906635 3609795068175386215359953)
          ·
            refine ⟨2707346301131539661519965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3609795068175386215359953 2707346301131539661519965)
            ·
              refine ⟨1015254862924327373069987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2707346301131539661519965 1015254862924327373069987)
              ·
                refine ⟨1522882294386491059604981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1015254862924327373069987 1522882294386491059604981)
                ·
                  refine ⟨142770215098733536837967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1522882294386491059604981 142770215098733536837967)
                  ·
                    rfl

theorem cell22_1251198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_1251198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1251198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1251198 prefixEnd_1251198 := by exact prefixLift 1251198
  have htrace : WordTrace (prefixWord ++ tailWord_1251198) baseStart_1251198 baseEnd_1251198 := by
    simpa [prefixWord, tailWord_1251198, baseEnd_1251198] using wordTrace_append hprefix tailTrace_1251198
  have hstable : (prefixWord ++ tailWord_1251198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251198).length < 2 ^ (prefixWord ++ tailWord_1251198).sum := by decide
  have hdescent : baseEnd_1251198 < baseStart_1251198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251226 : List Nat := [3, 1, 1, 4, 2, 1, 3, 3, 4]
def baseStart_1251226 : Nat := 118140960795 + 1251226 * 2 ^ 59
def prefixEnd_1251226 : Nat := 4983230072969 + 3 ^ 40 * 1251226 * 2
def baseEnd_1251226 : Nat := 142773410089472623604605

theorem tailTrace_1251226 : CollatzResearch.WordTrace tailWord_1251226 prefixEnd_1251226 142773410089472623604605 := by
  unfold tailWord_1251226
  simp only [CollatzResearch.WordTrace]
  refine ⟨11408990341257342308247383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30423974243352912821993021 11408990341257342308247383)
  ·
    refine ⟨17113485511886013462371075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11408990341257342308247383 17113485511886013462371075)
    ·
      refine ⟨25670228267829020193556613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17113485511886013462371075 25670228267829020193556613)
      ·
        refine ⟨4813167800217941286291865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25670228267829020193556613 4813167800217941286291865)
        ·
          refine ⟨3609875850163455964718899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4813167800217941286291865 3609875850163455964718899)
          ·
            refine ⟨5414813775245183947078349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3609875850163455964718899 5414813775245183947078349)
            ·
              refine ⟨2030555165716943980154381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5414813775245183947078349 2030555165716943980154381)
              ·
                refine ⟨761458187143853992557893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2030555165716943980154381 761458187143853992557893)
                ·
                  refine ⟨142773410089472623604605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 761458187143853992557893 142773410089472623604605)
                  ·
                    rfl

theorem cell22_1251226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 3, 4].length) (baseStart_1251226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1251226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1251226 prefixEnd_1251226 := by exact prefixLift 1251226
  have htrace : WordTrace (prefixWord ++ tailWord_1251226) baseStart_1251226 baseEnd_1251226 := by
    simpa [prefixWord, tailWord_1251226, baseEnd_1251226] using wordTrace_append hprefix tailTrace_1251226
  have hstable : (prefixWord ++ tailWord_1251226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251226).length < 2 ^ (prefixWord ++ tailWord_1251226).sum := by decide
  have hdescent : baseEnd_1251226 < baseStart_1251226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251239 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 4, 4]
def baseStart_1251239 : Nat := 118140960795 + 1251239 * 2 ^ 59
def prefixEnd_1251239 : Nat := 4983230072969 + 3 ^ 40 * 1251239 * 2
def baseEnd_1251239 : Nat := 428324680434090170238775

theorem tailTrace_1251239 : CollatzResearch.WordTrace tailWord_1251239 prefixEnd_1251239 428324680434090170238775 := by
  unfold tailWord_1251239
  simp only [CollatzResearch.WordTrace]
  refine ⟨45636435513982272453212771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30424290342654848302141847 45636435513982272453212771)
  ·
    refine ⟨68454653270973408679819157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45636435513982272453212771 68454653270973408679819157)
    ·
      refine ⟨3208811872076878531866523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 68454653270973408679819157 3208811872076878531866523)
      ·
        refine ⟨4813217808115317797799785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3208811872076878531866523 4813217808115317797799785)
        ·
          refine ⟨3609913356086488348349839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4813217808115317797799785 3609913356086488348349839)
          ·
            refine ⟨5414870034129732522524759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3609913356086488348349839 5414870034129732522524759)
            ·
              refine ⟨8122305051194598783787139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5414870034129732522524759 8122305051194598783787139)
              ·
                refine ⟨12183457576791898175680709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8122305051194598783787139 12183457576791898175680709)
                ·
                  refine ⟨2284398295648480907940133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12183457576791898175680709 2284398295648480907940133)
                  ·
                    refine ⟨428324680434090170238775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2284398295648480907940133 428324680434090170238775)
                    ·
                      rfl

theorem cell22_1251239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_1251239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1251239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1251239 prefixEnd_1251239 := by exact prefixLift 1251239
  have htrace : WordTrace (prefixWord ++ tailWord_1251239) baseStart_1251239 baseEnd_1251239 := by
    simpa [prefixWord, tailWord_1251239, baseEnd_1251239] using wordTrace_append hprefix tailTrace_1251239
  have hstable : (prefixWord ++ tailWord_1251239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251239).length < 2 ^ (prefixWord ++ tailWord_1251239).sum := by decide
  have hdescent : baseEnd_1251239 < baseStart_1251239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251292 : List Nat := [2, 2, 6, 1, 1, 1, 2, 2, 2, 3]
def baseStart_1251292 : Nat := 118140960795 + 1251292 * 2 ^ 59
def prefixEnd_1251292 : Nat := 4983230072969 + 3 ^ 40 * 1251292 * 2
def baseEnd_1251292 : Nat := 428342823417215698663613

theorem tailTrace_1251292 : CollatzResearch.WordTrace tailWord_1251292 prefixEnd_1251292 428342823417215698663613 := by
  unfold tailWord_1251292
  simp only [CollatzResearch.WordTrace]
  refine ⟨22819184291395131252446065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30425579055193508336594753 22819184291395131252446065)
  ·
    refine ⟨17114388218546348439334549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22819184291395131252446065 17114388218546348439334549)
    ·
      refine ⟨802236947744360083093807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17114388218546348439334549 802236947744360083093807)
      ·
        refine ⟨1203355421616540124640711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 802236947744360083093807 1203355421616540124640711)
        ·
          refine ⟨1805033132424810186961067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1203355421616540124640711 1805033132424810186961067)
          ·
            refine ⟨2707549698637215280441601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1805033132424810186961067 2707549698637215280441601)
            ·
              refine ⟨2030662273977911460331201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2707549698637215280441601 2030662273977911460331201)
              ·
                refine ⟨1522996705483433595248401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2030662273977911460331201 1522996705483433595248401)
                ·
                  refine ⟨1142247529112575196436301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1522996705483433595248401 1142247529112575196436301)
                  ·
                    refine ⟨428342823417215698663613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1142247529112575196436301 428342823417215698663613)
                    ·
                      rfl

theorem cell22_1251292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_1251292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1251292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1251292 prefixEnd_1251292 := by exact prefixLift 1251292
  have htrace : WordTrace (prefixWord ++ tailWord_1251292) baseStart_1251292 baseEnd_1251292 := by
    simpa [prefixWord, tailWord_1251292, baseEnd_1251292] using wordTrace_append hprefix tailTrace_1251292
  have hstable : (prefixWord ++ tailWord_1251292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251292).length < 2 ^ (prefixWord ++ tailWord_1251292).sum := by decide
  have hdescent : baseEnd_1251292 < baseStart_1251292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251299 : List Nat := [1, 1, 1, 6, 1, 2, 1, 4, 5]
def baseStart_1251299 : Nat := 118140960795 + 1251299 * 2 ^ 59
def prefixEnd_1251299 : Nat := 4983230072969 + 3 ^ 40 * 1251299 * 2
def baseEnd_1251299 : Nat := 142781739886756671246197

theorem tailTrace_1251299 : CollatzResearch.WordTrace tailWord_1251299 prefixEnd_1251299 142781739886756671246197 := by
  unfold tailWord_1251299
  simp only [CollatzResearch.WordTrace]
  refine ⟨45638623893764902700396951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30425749262509935133597967 45638623893764902700396951)
  ·
    refine ⟨68457935840647354050595427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45638623893764902700396951 68457935840647354050595427)
    ·
      refine ⟨102686903760971031075893141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68457935840647354050595427 102686903760971031075893141)
      ·
        refine ⟨4813448613795517081682491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 102686903760971031075893141 4813448613795517081682491)
        ·
          refine ⟨7220172920693275622523737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4813448613795517081682491 7220172920693275622523737)
          ·
            refine ⟨5415129690519956716892803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7220172920693275622523737 5415129690519956716892803)
            ·
              refine ⟨8122694535779935075339205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5415129690519956716892803 8122694535779935075339205)
              ·
                refine ⟨1523005225458737826626101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8122694535779935075339205 1523005225458737826626101)
                ·
                  refine ⟨142781739886756671246197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1523005225458737826626101 142781739886756671246197)
                  ·
                    rfl

theorem cell22_1251299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 5].length) (baseStart_1251299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1251299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1251299 prefixEnd_1251299 := by exact prefixLift 1251299
  have htrace : WordTrace (prefixWord ++ tailWord_1251299) baseStart_1251299 baseEnd_1251299 := by
    simpa [prefixWord, tailWord_1251299, baseEnd_1251299] using wordTrace_append hprefix tailTrace_1251299
  have hstable : (prefixWord ++ tailWord_1251299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251299).length < 2 ^ (prefixWord ++ tailWord_1251299).sum := by decide
  have hdescent : baseEnd_1251299 < baseStart_1251299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251329 : List Nat := [1, 2, 4, 1, 2, 1, 1, 3, 3, 4]
def baseStart_1251329 : Nat := 118140960795 + 1251329 * 2 ^ 59
def prefixEnd_1251329 : Nat := 4983230072969 + 3 ^ 40 * 1251329 * 2
def baseEnd_1251329 : Nat := 428355489273359935488499

theorem tailTrace_1251329 : CollatzResearch.WordTrace tailWord_1251329 prefixEnd_1251329 428355489273359935488499 := by
  unfold tailWord_1251329
  simp only [CollatzResearch.WordTrace]
  refine ⟨45639718083656217823989041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30426478722437478549326027 45639718083656217823989041)
  ·
    refine ⟨34229788562742163367991781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45639718083656217823989041 34229788562742163367991781)
    ·
      refine ⟨6418085355514155631498459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34229788562742163367991781 6418085355514155631498459)
      ·
        refine ⟨9627128033271233447247689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6418085355514155631498459 9627128033271233447247689)
        ·
          refine ⟨7220346024953425085435767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9627128033271233447247689 7220346024953425085435767)
          ·
            refine ⟨10830519037430137628153651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7220346024953425085435767 10830519037430137628153651)
            ·
              refine ⟨16245778556145206442230477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10830519037430137628153651 16245778556145206442230477)
              ·
                refine ⟨6092166958554452415836429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16245778556145206442230477 6092166958554452415836429)
                ·
                  refine ⟨2284562609457919655938661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6092166958554452415836429 2284562609457919655938661)
                  ·
                    refine ⟨428355489273359935488499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2284562609457919655938661 428355489273359935488499)
                    ·
                      rfl

theorem cell22_1251329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_1251329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1251329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1251329 prefixEnd_1251329 := by exact prefixLift 1251329
  have htrace : WordTrace (prefixWord ++ tailWord_1251329) baseStart_1251329 baseEnd_1251329 := by
    simpa [prefixWord, tailWord_1251329, baseEnd_1251329] using wordTrace_append hprefix tailTrace_1251329
  have hstable : (prefixWord ++ tailWord_1251329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251329).length < 2 ^ (prefixWord ++ tailWord_1251329).sum := by decide
  have hdescent : baseEnd_1251329 < baseStart_1251329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251361 : List Nat := [1, 2, 3, 2, 4, 1, 2, 1, 6]
def baseStart_1251361 : Nat := 118140960795 + 1251361 * 2 ^ 59
def prefixEnd_1251361 : Nat := 4983230072969 + 3 ^ 40 * 1251361 * 2
def baseEnd_1251361 : Nat := 142788814509107506229467

theorem tailTrace_1251361 : CollatzResearch.WordTrace tailWord_1251361 prefixEnd_1251361 142788814509107506229467 := by
  unfold tailWord_1251361
  simp only [CollatzResearch.WordTrace]
  refine ⟨45640885219540287289153937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30427256813026858192769291 45640885219540287289153937)
  ·
    refine ⟨34230663914655215466865453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45640885219540287289153937 34230663914655215466865453)
    ·
      refine ⟨12836498967995705800074545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34230663914655215466865453 12836498967995705800074545)
      ·
        refine ⟨9627374225996779350055909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12836498967995705800074545 9627374225996779350055909)
        ·
          refine ⟨1805132667374396128135483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9627374225996779350055909 1805132667374396128135483)
          ·
            refine ⟨2707699001061594192203225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1805132667374396128135483 2707699001061594192203225)
            ·
              refine ⟨2030774250796195644152419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2707699001061594192203225 2030774250796195644152419)
              ·
                refine ⟨3046161376194293466228629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2030774250796195644152419 3046161376194293466228629)
                ·
                  refine ⟨142788814509107506229467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3046161376194293466228629 142788814509107506229467)
                  ·
                    rfl

theorem cell22_1251361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 6].length) (baseStart_1251361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1251361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1251361 prefixEnd_1251361 := by exact prefixLift 1251361
  have htrace : WordTrace (prefixWord ++ tailWord_1251361) baseStart_1251361 baseEnd_1251361 := by
    simpa [prefixWord, tailWord_1251361, baseEnd_1251361] using wordTrace_append hprefix tailTrace_1251361
  have hstable : (prefixWord ++ tailWord_1251361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251361).length < 2 ^ (prefixWord ++ tailWord_1251361).sum := by decide
  have hdescent : baseEnd_1251361 < baseStart_1251361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251376 : List Nat := [2, 1, 1, 1, 2, 7, 1, 1, 1, 5]
def baseStart_1251376 : Nat := 118140960795 + 1251376 * 2 ^ 59
def prefixEnd_1251376 : Nat := 4983230072969 + 3 ^ 40 * 1251376 * 2
def baseEnd_1251376 : Nat := 428371578333867479563355

theorem tailTrace_1251376 : CollatzResearch.WordTrace tailWord_1251376 prefixEnd_1251376 428371578333867479563355 := by
  unfold tailWord_1251376
  simp only [CollatzResearch.WordTrace]
  refine ⟨22820716157242972425474991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30427621542990629900633321 22820716157242972425474991)
  ·
    refine ⟨34231074235864458638212487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22820716157242972425474991 34231074235864458638212487)
    ·
      refine ⟨51346611353796687957318731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34231074235864458638212487 51346611353796687957318731)
      ·
        refine ⟨77019917030695031935978097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51346611353796687957318731 77019917030695031935978097)
        ·
          refine ⟨57764937773021273951983573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77019917030695031935978097 57764937773021273951983573)
          ·
            refine ⟨1353865729055186108249615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 57764937773021273951983573 1353865729055186108249615)
            ·
              refine ⟨2030798593582779162374423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1353865729055186108249615 2030798593582779162374423)
              ·
                refine ⟨3046197890374168743561635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2030798593582779162374423 3046197890374168743561635)
                ·
                  refine ⟨4569296835561253115342453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3046197890374168743561635 4569296835561253115342453)
                  ·
                    refine ⟨428371578333867479563355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4569296835561253115342453 428371578333867479563355)
                    ·
                      rfl

theorem cell22_1251376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 1, 5].length) (baseStart_1251376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1251376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1251376 prefixEnd_1251376 := by exact prefixLift 1251376
  have htrace : WordTrace (prefixWord ++ tailWord_1251376) baseStart_1251376 baseEnd_1251376 := by
    simpa [prefixWord, tailWord_1251376, baseEnd_1251376] using wordTrace_append hprefix tailTrace_1251376
  have hstable : (prefixWord ++ tailWord_1251376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251376).length < 2 ^ (prefixWord ++ tailWord_1251376).sum := by decide
  have hdescent : baseEnd_1251376 < baseStart_1251376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251380 : List Nat := [2, 5, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_1251380 : Nat := 118140960795 + 1251380 * 2 ^ 59
def prefixEnd_1251380 : Nat := 4983230072969 + 3 ^ 40 * 1251380 * 2
def baseEnd_1251380 : Nat := 428372947615612802463343

theorem tailTrace_1251380 : CollatzResearch.WordTrace tailWord_1251380 prefixEnd_1251380 428372947615612802463343 := by
  unfold tailWord_1251380
  simp only [CollatzResearch.WordTrace]
  refine ⟨22820789103235726767047797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30427718804314302356063729 22820789103235726767047797)
  ·
    refine ⟨2139448978428349384410731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22820789103235726767047797 2139448978428349384410731)
    ·
      refine ⟨3209173467642524076616097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2139448978428349384410731 3209173467642524076616097)
      ·
        refine ⟨2406880100731893057462073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3209173467642524076616097 2406880100731893057462073)
        ·
          refine ⟨1805160075548919793096555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2406880100731893057462073 1805160075548919793096555)
          ·
            refine ⟨2707740113323379689644833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1805160075548919793096555 2707740113323379689644833)
            ·
              refine ⟨2030805084992534767233625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2707740113323379689644833 2030805084992534767233625)
              ·
                refine ⟨1523103813744401075425219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2030805084992534767233625 1523103813744401075425219)
                ·
                  refine ⟨2284655720616601613137829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1523103813744401075425219 2284655720616601613137829)
                  ·
                    refine ⟨428372947615612802463343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2284655720616601613137829 428372947615612802463343)
                    ·
                      rfl

theorem cell22_1251380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_1251380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1251380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1251380 prefixEnd_1251380 := by exact prefixLift 1251380
  have htrace : WordTrace (prefixWord ++ tailWord_1251380) baseStart_1251380 baseEnd_1251380 := by
    simpa [prefixWord, tailWord_1251380, baseEnd_1251380] using wordTrace_append hprefix tailTrace_1251380
  have hstable : (prefixWord ++ tailWord_1251380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251380).length < 2 ^ (prefixWord ++ tailWord_1251380).sum := by decide
  have hdescent : baseEnd_1251380 < baseStart_1251380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251389 : List Nat := [1, 4, 1, 3, 1, 1, 3, 8]
def baseStart_1251389 : Nat := 118140960795 + 1251389 * 2 ^ 59
def prefixEnd_1251389 : Nat := 4983230072969 + 3 ^ 40 * 1251389 * 2
def baseEnd_1251389 : Nat := 47597336499948864332035

theorem tailTrace_1251389 : CollatzResearch.WordTrace tailWord_1251389 prefixEnd_1251389 47597336499948864332035 := by
  unfold tailWord_1251389
  simp only [CollatzResearch.WordTrace]
  refine ⟨45641906463438848071173221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30427937642292565380782147 45641906463438848071173221)
  ·
    refine ⟨8557857461894784013344979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45641906463438848071173221 8557857461894784013344979)
    ·
      refine ⟨12836786192842176020017469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8557857461894784013344979 12836786192842176020017469)
      ·
        refine ⟨4813794822315816007506551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12836786192842176020017469 4813794822315816007506551)
        ·
          refine ⟨7220692233473724011259827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4813794822315816007506551 7220692233473724011259827)
          ·
            refine ⟨10831038350210586016889741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7220692233473724011259827 10831038350210586016889741)
            ·
              refine ⟨4061639381328969756333653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10831038350210586016889741 4061639381328969756333653)
              ·
                refine ⟨47597336499948864332035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4061639381328969756333653 47597336499948864332035)
                ·
                  rfl

theorem cell22_1251389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 8].length) (baseStart_1251389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1251389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1251389 prefixEnd_1251389 := by exact prefixLift 1251389
  have htrace : WordTrace (prefixWord ++ tailWord_1251389) baseStart_1251389 baseEnd_1251389 := by
    simpa [prefixWord, tailWord_1251389, baseEnd_1251389] using wordTrace_append hprefix tailTrace_1251389
  have hstable : (prefixWord ++ tailWord_1251389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251389).length < 2 ^ (prefixWord ++ tailWord_1251389).sum := by decide
  have hdescent : baseEnd_1251389 < baseStart_1251389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251511 : List Nat := [1, 1, 3, 1, 4, 2, 2, 2, 1, 5]
def baseStart_1251511 : Nat := 118140960795 + 1251511 * 2 ^ 59
def prefixEnd_1251511 : Nat := 4983230072969 + 3 ^ 40 * 1251511 * 2
def baseEnd_1251511 : Nat := 428417791592772127437941

theorem tailTrace_1251511 : CollatzResearch.WordTrace tailWord_1251511 prefixEnd_1251511 428417791592772127437941 := by
  unfold tailWord_1251511
  simp only [CollatzResearch.WordTrace]
  refine ⟨45646356168996862907114387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30430904112664575271409591 45646356168996862907114387)
  ·
    refine ⟨68469534253495294360671581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45646356168996862907114387 68469534253495294360671581)
    ·
      refine ⟨25676075345060735385251843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68469534253495294360671581 25676075345060735385251843)
      ·
        refine ⟨38514113017591103077877765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25676075345060735385251843 38514113017591103077877765)
        ·
          refine ⟨7221396190798331827102081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38514113017591103077877765 7221396190798331827102081)
          ·
            refine ⟨5416047143098748870326561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7221396190798331827102081 5416047143098748870326561)
            ·
              refine ⟨4062035357324061652744921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5416047143098748870326561 4062035357324061652744921)
              ·
                refine ⟨3046526517993046239558691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4062035357324061652744921 3046526517993046239558691)
                ·
                  refine ⟨4569789776989569359338037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3046526517993046239558691 4569789776989569359338037)
                  ·
                    refine ⟨428417791592772127437941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4569789776989569359338037 428417791592772127437941)
                    ·
                      rfl

theorem cell22_1251511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_1251511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1251511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1251511 prefixEnd_1251511 := by exact prefixLift 1251511
  have htrace : WordTrace (prefixWord ++ tailWord_1251511) baseStart_1251511 baseEnd_1251511 := by
    simpa [prefixWord, tailWord_1251511, baseEnd_1251511] using wordTrace_append hprefix tailTrace_1251511
  have hstable : (prefixWord ++ tailWord_1251511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251511).length < 2 ^ (prefixWord ++ tailWord_1251511).sum := by decide
  have hdescent : baseEnd_1251511 < baseStart_1251511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251513 : List Nat := [1, 2, 1, 4, 1, 2, 4, 3, 4]
def baseStart_1251513 : Nat := 118140960795 + 1251513 * 2 ^ 59
def prefixEnd_1251513 : Nat := 4983230072969 + 3 ^ 40 * 1251513 * 2
def baseEnd_1251513 : Nat := 142806158744548262962645

theorem tailTrace_1251513 : CollatzResearch.WordTrace tailWord_1251513 prefixEnd_1251513 142806158744548262962645 := by
  unfold tailWord_1251513
  simp only [CollatzResearch.WordTrace]
  refine ⟨45646429114989617248687193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30430952743326411499124795 45646429114989617248687193)
  ·
    refine ⟨34234821836242212936515395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45646429114989617248687193 34234821836242212936515395)
    ·
      refine ⟨51352232754363319404773093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34234821836242212936515395 51352232754363319404773093)
      ·
        refine ⟨9628543641443122388394955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51352232754363319404773093 9628543641443122388394955)
        ·
          refine ⟨14442815462164683582592433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9628543641443122388394955 14442815462164683582592433)
          ·
            refine ⟨10832111596623512686944325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14442815462164683582592433 10832111596623512686944325)
            ·
              refine ⟨2031020924366908628802061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10832111596623512686944325 2031020924366908628802061)
              ·
                refine ⟨761632846637590735800773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2031020924366908628802061 761632846637590735800773)
                ·
                  refine ⟨142806158744548262962645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 761632846637590735800773 142806158744548262962645)
                  ·
                    rfl

theorem cell22_1251513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 3, 4].length) (baseStart_1251513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1251513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1251513 prefixEnd_1251513 := by exact prefixLift 1251513
  have htrace : WordTrace (prefixWord ++ tailWord_1251513) baseStart_1251513 baseEnd_1251513 := by
    simpa [prefixWord, tailWord_1251513, baseEnd_1251513] using wordTrace_append hprefix tailTrace_1251513
  have hstable : (prefixWord ++ tailWord_1251513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251513).length < 2 ^ (prefixWord ++ tailWord_1251513).sum := by decide
  have hdescent : baseEnd_1251513 < baseStart_1251513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251539 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 4, 7]
def baseStart_1251539 : Nat := 118140960795 + 1251539 * 2 ^ 59
def prefixEnd_1251539 : Nat := 4983230072969 + 3 ^ 40 * 1251539 * 2
def baseEnd_1251539 : Nat := 428427376564989387737855

theorem tailTrace_1251539 : CollatzResearch.WordTrace tailWord_1251539 prefixEnd_1251539 428427376564989387737855 := by
  unfold tailWord_1251539
  simp only [CollatzResearch.WordTrace]
  refine ⟨45647377412895423689133671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30431584941930282459422447 45647377412895423689133671)
  ·
    refine ⟨68471066119343135533700507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45647377412895423689133671 68471066119343135533700507)
    ·
      refine ⟨102706599179014703300550761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68471066119343135533700507 102706599179014703300550761)
      ·
        refine ⟨77029949384261027475413071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102706599179014703300550761 77029949384261027475413071)
        ·
          refine ⟨115544924076391541213119607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77029949384261027475413071 115544924076391541213119607)
          ·
            refine ⟨173317386114587311819679411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115544924076391541213119607 173317386114587311819679411)
            ·
              refine ⟨259976079171880967729519117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173317386114587311819679411 259976079171880967729519117)
              ·
                refine ⟨97491029689455362898569669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 259976079171880967729519117 97491029689455362898569669)
                ·
                  refine ⟨18279568066772880543481813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97491029689455362898569669 18279568066772880543481813)
                  ·
                    refine ⟨428427376564989387737855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18279568066772880543481813 428427376564989387737855)
                    ·
                      rfl

theorem cell22_1251539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 7].length) (baseStart_1251539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1251539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1251539 prefixEnd_1251539 := by exact prefixLift 1251539
  have htrace : WordTrace (prefixWord ++ tailWord_1251539) baseStart_1251539 baseEnd_1251539 := by
    simpa [prefixWord, tailWord_1251539, baseEnd_1251539] using wordTrace_append hprefix tailTrace_1251539
  have hstable : (prefixWord ++ tailWord_1251539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251539).length < 2 ^ (prefixWord ++ tailWord_1251539).sum := by decide
  have hdescent : baseEnd_1251539 < baseStart_1251539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251682 : List Nat := [3, 3, 2, 1, 1, 3, 2, 3, 4]
def baseStart_1251682 : Nat := 118140960795 + 1251682 * 2 ^ 59
def prefixEnd_1251682 : Nat := 4983230072969 + 3 ^ 40 * 1251682 * 2
def baseEnd_1251682 : Nat := 142825442795794893804139

theorem tailTrace_1251682 : CollatzResearch.WordTrace tailWord_1251682 prefixEnd_1251682 142825442795794893804139 := by
  unfold tailWord_1251682
  simp only [CollatzResearch.WordTrace]
  refine ⟨11413148262844339777897325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30435062034251572741059533 11413148262844339777897325)
  ·
    refine ⟨4279930598566627416711497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11413148262844339777897325 4279930598566627416711497)
    ·
      refine ⟨3209947948924970562533623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4279930598566627416711497 3209947948924970562533623)
      ·
        refine ⟨4814921923387455843800435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3209947948924970562533623 4814921923387455843800435)
        ·
          refine ⟨7222382885081183765700653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4814921923387455843800435 7222382885081183765700653)
          ·
            refine ⟨2708393581905443912137745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7222382885081183765700653 2708393581905443912137745)
            ·
              refine ⟨2031295186429082934103309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2708393581905443912137745 2031295186429082934103309)
              ·
                refine ⟨761735694910906100288741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2031295186429082934103309 761735694910906100288741)
                ·
                  refine ⟨142825442795794893804139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 761735694910906100288741 142825442795794893804139)
                  ·
                    rfl

theorem cell22_1251682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_1251682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1251682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1251682 prefixEnd_1251682 := by exact prefixLift 1251682
  have htrace : WordTrace (prefixWord ++ tailWord_1251682) baseStart_1251682 baseEnd_1251682 := by
    simpa [prefixWord, tailWord_1251682, baseEnd_1251682] using wordTrace_append hprefix tailTrace_1251682
  have hstable : (prefixWord ++ tailWord_1251682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251682).length < 2 ^ (prefixWord ++ tailWord_1251682).sum := by decide
  have hdescent : baseEnd_1251682 < baseStart_1251682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251714 : List Nat := [3, 4, 2, 1, 2, 2, 1, 1, 1, 5]
def baseStart_1251714 : Nat := 118140960795 + 1251714 * 2 ^ 59
def prefixEnd_1251714 : Nat := 4983230072969 + 3 ^ 40 * 1251714 * 2
def baseEnd_1251714 : Nat := 428487282641347264612319

theorem tailTrace_1251714 : CollatzResearch.WordTrace tailWord_1251714 prefixEnd_1251714 428487282641347264612319 := by
  unfold tailWord_1251714
  simp only [CollatzResearch.WordTrace]
  refine ⟨11413440046815357144188549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30435840124840952384502797 11413440046815357144188549)
  ·
    refine ⟨2140020008777879464535353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11413440046815357144188549 2140020008777879464535353)
    ·
      refine ⟨1605015006583409598401515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2140020008777879464535353 1605015006583409598401515)
      ·
        refine ⟨2407522509875114397602273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1605015006583409598401515 2407522509875114397602273)
        ·
          refine ⟨1805641882406335798201705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2407522509875114397602273 1805641882406335798201705)
          ·
            refine ⟨1354231411804751848651279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1805641882406335798201705 1354231411804751848651279)
            ·
              refine ⟨2031347117707127772976919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1354231411804751848651279 2031347117707127772976919)
              ·
                refine ⟨3047020676560691659465379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2031347117707127772976919 3047020676560691659465379)
                ·
                  refine ⟨4570531014841037489198069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3047020676560691659465379 4570531014841037489198069)
                  ·
                    refine ⟨428487282641347264612319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4570531014841037489198069 428487282641347264612319)
                    ·
                      rfl

theorem cell22_1251714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_1251714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1251714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1251714 prefixEnd_1251714 := by exact prefixLift 1251714
  have htrace : WordTrace (prefixWord ++ tailWord_1251714) baseStart_1251714 baseEnd_1251714 := by
    simpa [prefixWord, tailWord_1251714, baseEnd_1251714] using wordTrace_append hprefix tailTrace_1251714
  have hstable : (prefixWord ++ tailWord_1251714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251714).length < 2 ^ (prefixWord ++ tailWord_1251714).sum := by decide
  have hdescent : baseEnd_1251714 < baseStart_1251714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251738 : List Nat := [3, 1, 1, 4, 1, 2, 1, 2, 7]
def baseStart_1251738 : Nat := 118140960795 + 1251738 * 2 ^ 59
def prefixEnd_1251738 : Nat := 4983230072969 + 3 ^ 40 * 1251738 * 2
def baseEnd_1251738 : Nat := 142831832777273067337415

theorem tailTrace_1251738 : CollatzResearch.WordTrace tailWord_1251738 prefixEnd_1251738 142831832777273067337415 := by
  unfold tailWord_1251738
  simp only [CollatzResearch.WordTrace]
  refine ⟨11413658884793620168906967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30436423692782987117085245 11413658884793620168906967)
  ·
    refine ⟨17120488327190430253360451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11413658884793620168906967 17120488327190430253360451)
    ·
      refine ⟨25680732490785645380040677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17120488327190430253360451 25680732490785645380040677)
      ·
        refine ⟨4815137342022308508757627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25680732490785645380040677 4815137342022308508757627)
        ·
          refine ⟨7222706013033462763136441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4815137342022308508757627 7222706013033462763136441)
          ·
            refine ⟨5417029509775097072352331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7222706013033462763136441 5417029509775097072352331)
            ·
              refine ⟨8125544264662645608528497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5417029509775097072352331 8125544264662645608528497)
              ·
                refine ⟨6094158198496984206396373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8125544264662645608528497 6094158198496984206396373)
                ·
                  refine ⟨142831832777273067337415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6094158198496984206396373 142831832777273067337415)
                  ·
                    rfl

theorem cell22_1251738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 7].length) (baseStart_1251738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1251738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1251738 prefixEnd_1251738 := by exact prefixLift 1251738
  have htrace : WordTrace (prefixWord ++ tailWord_1251738) baseStart_1251738 baseEnd_1251738 := by
    simpa [prefixWord, tailWord_1251738, baseEnd_1251738] using wordTrace_append hprefix tailTrace_1251738
  have hstable : (prefixWord ++ tailWord_1251738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251738).length < 2 ^ (prefixWord ++ tailWord_1251738).sum := by decide
  have hdescent : baseEnd_1251738 < baseStart_1251738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251768 : List Nat := [2, 1, 2, 1, 2, 2, 1, 4, 3, 4]
def baseStart_1251768 : Nat := 118140960795 + 1251768 * 2 ^ 59
def prefixEnd_1251768 : Nat := 4983230072969 + 3 ^ 40 * 1251768 * 2
def baseEnd_1251768 : Nat := 428505767944909123762153

theorem tailTrace_1251768 : CollatzResearch.WordTrace tailWord_1251768 prefixEnd_1251768 428505767944909123762153 := by
  unfold tailWord_1251768
  simp only [CollatzResearch.WordTrace]
  refine ⟨22827864864532897899609979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30437153152710530532813305 22827864864532897899609979)
  ·
    refine ⟨34241797296799346849414969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22827864864532897899609979 34241797296799346849414969)
    ·
      refine ⟨25681347972599510137061227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34241797296799346849414969 25681347972599510137061227)
      ·
        refine ⟨38522021958899265205591841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25681347972599510137061227 38522021958899265205591841)
        ·
          refine ⟨28891516469174448904193881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38522021958899265205591841 28891516469174448904193881)
          ·
            refine ⟨21668637351880836678145411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28891516469174448904193881 21668637351880836678145411)
            ·
              refine ⟨32502956027821255017218117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21668637351880836678145411 32502956027821255017218117)
              ·
                refine ⟨6094304255216485315728397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32502956027821255017218117 6094304255216485315728397)
                ·
                  refine ⟨2285364095706181993398149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6094304255216485315728397 2285364095706181993398149)
                  ·
                    refine ⟨428505767944909123762153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2285364095706181993398149 428505767944909123762153)
                    ·
                      rfl

theorem cell22_1251768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_1251768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1251768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1251768 prefixEnd_1251768 := by exact prefixLift 1251768
  have htrace : WordTrace (prefixWord ++ tailWord_1251768) baseStart_1251768 baseEnd_1251768 := by
    simpa [prefixWord, tailWord_1251768, baseEnd_1251768] using wordTrace_append hprefix tailTrace_1251768
  have hstable : (prefixWord ++ tailWord_1251768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251768).length < 2 ^ (prefixWord ++ tailWord_1251768).sum := by decide
  have hdescent : baseEnd_1251768 < baseStart_1251768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251772 : List Nat := [2, 2, 2, 4, 1, 1, 4, 1, 5]
def baseStart_1251772 : Nat := 118140960795 + 1251772 * 2 ^ 59
def prefixEnd_1251772 : Nat := 4983230072969 + 3 ^ 40 * 1251772 * 2
def baseEnd_1251772 : Nat := 142835712408884815554047

theorem tailTrace_1251772 : CollatzResearch.WordTrace tailWord_1251772 prefixEnd_1251772 142835712408884815554047 := by
  unfold tailWord_1251772
  simp only [CollatzResearch.WordTrace]
  refine ⟨22827937810525652241182785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30437250414034202988243713 22827937810525652241182785)
  ·
    refine ⟨17120953357894239180887089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22827937810525652241182785 17120953357894239180887089)
    ·
      refine ⟨12840715018420679385665317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17120953357894239180887089 12840715018420679385665317)
      ·
        refine ⟨2407634065953877384812247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12840715018420679385665317 2407634065953877384812247)
        ·
          refine ⟨3611451098930816077218371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2407634065953877384812247 3611451098930816077218371)
          ·
            refine ⟨5417176648396224115827557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3611451098930816077218371 5417176648396224115827557)
            ·
              refine ⟨1015720621574292021717667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5417176648396224115827557 1015720621574292021717667)
              ·
                refine ⟨1523580932361438032576501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1015720621574292021717667 1523580932361438032576501)
                ·
                  refine ⟨142835712408884815554047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1523580932361438032576501 142835712408884815554047)
                  ·
                    rfl

theorem cell22_1251772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 5].length) (baseStart_1251772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1251772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1251772 prefixEnd_1251772 := by exact prefixLift 1251772
  have htrace : WordTrace (prefixWord ++ tailWord_1251772) baseStart_1251772 baseEnd_1251772 := by
    simpa [prefixWord, tailWord_1251772, baseEnd_1251772] using wordTrace_append hprefix tailTrace_1251772
  have hstable : (prefixWord ++ tailWord_1251772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251772).length < 2 ^ (prefixWord ++ tailWord_1251772).sum := by decide
  have hdescent : baseEnd_1251772 < baseStart_1251772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251785 : List Nat := [1, 2, 1, 1, 2, 1, 7, 2, 1, 4]
def baseStart_1251785 : Nat := 118140960795 + 1251785 * 2 ^ 59
def prefixEnd_1251785 : Nat := 4983230072969 + 3 ^ 40 * 1251785 * 2
def baseEnd_1251785 : Nat := 428511587392326746087101

theorem tailTrace_1251785 : CollatzResearch.WordTrace tailWord_1251785 prefixEnd_1251785 428511587392326746087101 := by
  unfold tailWord_1251785
  simp only [CollatzResearch.WordTrace]
  refine ⟨45656349770004207702588809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30437566513336138468392539 45656349770004207702588809)
  ·
    refine ⟨34242262327503155776941607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45656349770004207702588809 34242262327503155776941607)
    ·
      refine ⟨51363393491254733665412411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34242262327503155776941607 51363393491254733665412411)
      ·
        refine ⟨77045090236882100498118617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51363393491254733665412411 77045090236882100498118617)
        ·
          refine ⟨57783817677661575373588963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77045090236882100498118617 57783817677661575373588963)
          ·
            refine ⟨86675726516492363060383445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57783817677661575373588963 86675726516492363060383445)
            ·
              refine ⟨2031462340230289759227737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 86675726516492363060383445 2031462340230289759227737)
              ·
                refine ⟨1523596755172717319420803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2031462340230289759227737 1523596755172717319420803)
                ·
                  refine ⟨2285395132759075979131205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1523596755172717319420803 2285395132759075979131205)
                  ·
                    refine ⟨428511587392326746087101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2285395132759075979131205 428511587392326746087101)
                    ·
                      rfl

theorem cell22_1251785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 4].length) (baseStart_1251785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1251785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1251785 prefixEnd_1251785 := by exact prefixLift 1251785
  have htrace : WordTrace (prefixWord ++ tailWord_1251785) baseStart_1251785 baseEnd_1251785 := by
    simpa [prefixWord, tailWord_1251785, baseEnd_1251785] using wordTrace_append hprefix tailTrace_1251785
  have hstable : (prefixWord ++ tailWord_1251785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251785).length < 2 ^ (prefixWord ++ tailWord_1251785).sum := by decide
  have hdescent : baseEnd_1251785 < baseStart_1251785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251800 : List Nat := [2, 1, 2, 2, 2, 1, 1, 7, 4]
def baseStart_1251800 : Nat := 118140960795 + 1251800 * 2 ^ 59
def prefixEnd_1251800 : Nat := 4983230072969 + 3 ^ 40 * 1251800 * 2
def baseEnd_1251800 : Nat := 142838907399623902320685

theorem tailTrace_1251800 : CollatzResearch.WordTrace tailWord_1251800 prefixEnd_1251800 142838907399623902320685 := by
  unfold tailWord_1251800
  simp only [CollatzResearch.WordTrace]
  refine ⟨22828448432474932632192427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30437931243299910176256569 22828448432474932632192427)
  ·
    refine ⟨34242672648712398948288641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22828448432474932632192427 34242672648712398948288641)
    ·
      refine ⟨25682004486534299211216481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34242672648712398948288641 25682004486534299211216481)
      ·
        refine ⟨19261503364900724408412361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25682004486534299211216481 19261503364900724408412361)
        ·
          refine ⟨14446127523675543306309271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19261503364900724408412361 14446127523675543306309271)
          ·
            refine ⟨21669191285513314959463907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14446127523675543306309271 21669191285513314959463907)
            ·
              refine ⟨32503786928269972439195861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21669191285513314959463907 32503786928269972439195861)
              ·
                refine ⟨761807506131327479043653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 32503786928269972439195861 761807506131327479043653)
                ·
                  refine ⟨142838907399623902320685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 761807506131327479043653 142838907399623902320685)
                  ·
                    rfl

theorem cell22_1251800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 7, 4].length) (baseStart_1251800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1251800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1251800 prefixEnd_1251800 := by exact prefixLift 1251800
  have htrace : WordTrace (prefixWord ++ tailWord_1251800) baseStart_1251800 baseEnd_1251800 := by
    simpa [prefixWord, tailWord_1251800, baseEnd_1251800] using wordTrace_append hprefix tailTrace_1251800
  have hstable : (prefixWord ++ tailWord_1251800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251800).length < 2 ^ (prefixWord ++ tailWord_1251800).sum := by decide
  have hdescent : baseEnd_1251800 < baseStart_1251800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251802 : List Nat := [3, 1, 1, 2, 3, 1, 5, 1, 1, 4]
def baseStart_1251802 : Nat := 118140960795 + 1251802 * 2 ^ 59
def prefixEnd_1251802 : Nat := 4983230072969 + 3 ^ 40 * 1251802 * 2
def baseEnd_1251802 : Nat := 428517406839744368412049

theorem tailTrace_1251802 : CollatzResearch.WordTrace tailWord_1251802 prefixEnd_1251802 428517406839744368412049 := by
  unfold tailWord_1251802
  simp only [CollatzResearch.WordTrace]
  refine ⟨11414242452735654901489415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30437979873961746403971773 11414242452735654901489415)
  ·
    refine ⟨17121363679103482352234123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11414242452735654901489415 17121363679103482352234123)
    ·
      refine ⟨25682045518655223528351185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17121363679103482352234123 25682045518655223528351185)
      ·
        refine ⟨19261534138991417646263389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25682045518655223528351185 19261534138991417646263389)
        ·
          refine ⟨7223075302121781617348771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19261534138991417646263389 7223075302121781617348771)
          ·
            refine ⟨10834612953182672426023157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7223075302121781617348771 10834612953182672426023157)
            ·
              refine ⟨1015744964360875539939671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10834612953182672426023157 1015744964360875539939671)
              ·
                refine ⟨1523617446541313309909507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1015744964360875539939671 1523617446541313309909507)
                ·
                  refine ⟨2285426169811969964864261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1523617446541313309909507 2285426169811969964864261)
                  ·
                    refine ⟨428517406839744368412049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2285426169811969964864261 428517406839744368412049)
                    ·
                      rfl

theorem cell22_1251802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 1, 4].length) (baseStart_1251802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1251802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1251802 prefixEnd_1251802 := by exact prefixLift 1251802
  have htrace : WordTrace (prefixWord ++ tailWord_1251802) baseStart_1251802 baseEnd_1251802 := by
    simpa [prefixWord, tailWord_1251802, baseEnd_1251802] using wordTrace_append hprefix tailTrace_1251802
  have hstable : (prefixWord ++ tailWord_1251802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251802).length < 2 ^ (prefixWord ++ tailWord_1251802).sum := by decide
  have hdescent : baseEnd_1251802 < baseStart_1251802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251810 : List Nat := [3, 3, 3, 2, 1, 2, 2, 2, 1, 3]
def baseStart_1251810 : Nat := 118140960795 + 1251810 * 2 ^ 59
def prefixEnd_1251810 : Nat := 4983230072969 + 3 ^ 40 * 1251810 * 2
def baseEnd_1251810 : Nat := 428520145403235014212025

theorem tailTrace_1251810 : CollatzResearch.WordTrace tailWord_1251810 prefixEnd_1251810 428520145403235014212025 := by
  unfold tailWord_1251810
  simp only [CollatzResearch.WordTrace]
  refine ⟨11414315398728409243062221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30438174396609091314832589 11414315398728409243062221)
  ·
    refine ⟨4280368274523153466148333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11414315398728409243062221 4280368274523153466148333)
    ·
      refine ⟨1605138102946182549805625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4280368274523153466148333 1605138102946182549805625)
      ·
        refine ⟨1203853577209636912354219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1605138102946182549805625 1203853577209636912354219)
        ·
          refine ⟨1805780365814455368531329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1203853577209636912354219 1805780365814455368531329)
          ·
            refine ⟨1354335274360841526398497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1805780365814455368531329 1354335274360841526398497)
            ·
              refine ⟨1015751455770631144798873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1354335274360841526398497 1015751455770631144798873)
              ·
                refine ⟨761813591827973358599155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1015751455770631144798873 761813591827973358599155)
                ·
                  refine ⟨1142720387741960037898733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 761813591827973358599155 1142720387741960037898733)
                  ·
                    refine ⟨428520145403235014212025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1142720387741960037898733 428520145403235014212025)
                    ·
                      rfl

theorem cell22_1251810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_1251810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1251810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1251810 prefixEnd_1251810 := by exact prefixLift 1251810
  have htrace : WordTrace (prefixWord ++ tailWord_1251810) baseStart_1251810 baseEnd_1251810 := by
    simpa [prefixWord, tailWord_1251810, baseEnd_1251810] using wordTrace_append hprefix tailTrace_1251810
  have hstable : (prefixWord ++ tailWord_1251810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251810).length < 2 ^ (prefixWord ++ tailWord_1251810).sum := by decide
  have hdescent : baseEnd_1251810 < baseStart_1251810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251830 : List Nat := [5, 1, 1, 1, 2, 1, 2, 2, 1, 6]
def baseStart_1251830 : Nat := 118140960795 + 1251830 * 2 ^ 59
def prefixEnd_1251830 : Nat := 4983230072969 + 3 ^ 40 * 1251830 * 2
def baseEnd_1251830 : Nat := 428526991811961628711963

theorem tailTrace_1251830 : CollatzResearch.WordTrace tailWord_1251830 prefixEnd_1251830 428526991811961628711963 := by
  unfold tailWord_1251830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2853624440927573774248559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30438660703227453591984629 2853624440927573774248559)
  ·
    refine ⟨4280436661391360661372839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2853624440927573774248559 4280436661391360661372839)
    ·
      refine ⟨6420654992087040992059259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4280436661391360661372839 6420654992087040992059259)
      ·
        refine ⟨9630982488130561488088889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6420654992087040992059259 9630982488130561488088889)
        ·
          refine ⟨7223236866097921116066667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9630982488130561488088889 7223236866097921116066667)
          ·
            refine ⟨10834855299146881674100001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7223236866097921116066667 10834855299146881674100001)
            ·
              refine ⟨8126141474360161255575001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10834855299146881674100001 8126141474360161255575001)
              ·
                refine ⟨6094606105770120941681251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8126141474360161255575001 6094606105770120941681251)
                ·
                  refine ⟨9141909158655181412521877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6094606105770120941681251 9141909158655181412521877)
                  ·
                    refine ⟨428526991811961628711963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9141909158655181412521877 428526991811961628711963)
                    ·
                      rfl

theorem cell22_1251830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_1251830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1251830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1251830 prefixEnd_1251830 := by exact prefixLift 1251830
  have htrace : WordTrace (prefixWord ++ tailWord_1251830) baseStart_1251830 baseEnd_1251830 := by
    simpa [prefixWord, tailWord_1251830, baseEnd_1251830] using wordTrace_append hprefix tailTrace_1251830
  have hstable : (prefixWord ++ tailWord_1251830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251830).length < 2 ^ (prefixWord ++ tailWord_1251830).sum := by decide
  have hdescent : baseEnd_1251830 < baseStart_1251830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251853 : List Nat := [1, 7, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_1251853 : Nat := 118140960795 + 1251853 * 2 ^ 59
def prefixEnd_1251853 : Nat := 4983230072969 + 3 ^ 40 * 1251853 * 2
def baseEnd_1251853 : Nat := 428534865181997235386893

theorem tailTrace_1251853 : CollatzResearch.WordTrace tailWord_1251853 prefixEnd_1251853 428534865181997235386893 := by
  unfold tailWord_1251853
  simp only [CollatzResearch.WordTrace]
  refine ⟨45658829933757855316064213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30439219955838570210709475 45658829933757855316064213)
  ·
    refine ⟨1070128826572449733970255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 45658829933757855316064213 1070128826572449733970255)
    ·
      refine ⟨1605193239858674600955383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1070128826572449733970255 1605193239858674600955383)
      ·
        refine ⟨2407789859788011901433075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1605193239858674600955383 2407789859788011901433075)
        ·
          refine ⟨3611684789682017852149613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2407789859788011901433075 3611684789682017852149613)
          ·
            refine ⟨1354381796130756694556105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3611684789682017852149613 1354381796130756694556105)
            ·
              refine ⟨1015786347098067520917079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1354381796130756694556105 1015786347098067520917079)
              ·
                refine ⟨1523679520647101281375619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1015786347098067520917079 1523679520647101281375619)
                ·
                  refine ⟨2285519280970651922063429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1523679520647101281375619 2285519280970651922063429)
                  ·
                    refine ⟨428534865181997235386893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2285519280970651922063429 428534865181997235386893)
                    ·
                      rfl

theorem cell22_1251853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_1251853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1251853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1251853 prefixEnd_1251853 := by exact prefixLift 1251853
  have htrace : WordTrace (prefixWord ++ tailWord_1251853) baseStart_1251853 baseEnd_1251853 := by
    simpa [prefixWord, tailWord_1251853, baseEnd_1251853] using wordTrace_append hprefix tailTrace_1251853
  have hstable : (prefixWord ++ tailWord_1251853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251853).length < 2 ^ (prefixWord ++ tailWord_1251853).sum := by decide
  have hdescent : baseEnd_1251853 < baseStart_1251853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251890 : List Nat := [3, 2, 1, 1, 2, 1, 2, 5, 5]
def baseStart_1251890 : Nat := 118140960795 + 1251890 * 2 ^ 59
def prefixEnd_1251890 : Nat := 4983230072969 + 3 ^ 40 * 1251890 * 2
def baseEnd_1251890 : Nat := 142849177012713824070593

theorem tailTrace_1251890 : CollatzResearch.WordTrace tailWord_1251890 prefixEnd_1251890 142849177012713824070593 := by
  unfold tailWord_1251890
  simp only [CollatzResearch.WordTrace]
  refine ⟨11415044858655952658790281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30440119623082540423440749 11415044858655952658790281)
  ·
    refine ⟨8561283643991964494092711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11415044858655952658790281 8561283643991964494092711)
    ·
      refine ⟨12841925465987946741139067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8561283643991964494092711 12841925465987946741139067)
      ·
        refine ⟨19262888198981920111708601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12841925465987946741139067 19262888198981920111708601)
        ·
          refine ⟨14447166149236440083781451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19262888198981920111708601 14447166149236440083781451)
          ·
            refine ⟨21670749223854660125672177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14447166149236440083781451 21670749223854660125672177)
            ·
              refine ⟨16253061917890995094254133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21670749223854660125672177 16253061917890995094254133)
              ·
                refine ⟨1523724554802280790086325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16253061917890995094254133 1523724554802280790086325)
                ·
                  refine ⟨142849177012713824070593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1523724554802280790086325 142849177012713824070593)
                  ·
                    rfl

theorem cell22_1251890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_1251890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1251890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1251890 prefixEnd_1251890 := by exact prefixLift 1251890
  have htrace : WordTrace (prefixWord ++ tailWord_1251890) baseStart_1251890 baseEnd_1251890 := by
    simpa [prefixWord, tailWord_1251890, baseEnd_1251890] using wordTrace_append hprefix tailTrace_1251890
  have hstable : (prefixWord ++ tailWord_1251890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251890).length < 2 ^ (prefixWord ++ tailWord_1251890).sum := by decide
  have hdescent : baseEnd_1251890 < baseStart_1251890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251894 : List Nat := [5, 1, 2, 1, 2, 1, 2, 2, 3, 3]
def baseStart_1251894 : Nat := 118140960795 + 1251894 * 2 ^ 59
def prefixEnd_1251894 : Nat := 4983230072969 + 3 ^ 40 * 1251894 * 2
def baseEnd_1251894 : Nat := 428548900319886795111767

theorem tailTrace_1251894 : CollatzResearch.WordTrace tailWord_1251894 prefixEnd_1251894 428548900319886795111767 := by
  unfold tailWord_1251894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2853770332913082457394171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30440216884406212878871157 2853770332913082457394171)
  ·
    refine ⟨4280655499369623686091257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2853770332913082457394171 4280655499369623686091257)
    ·
      refine ⟨3210491624527217764568443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4280655499369623686091257 3210491624527217764568443)
      ·
        refine ⟨4815737436790826646852665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3210491624527217764568443 4815737436790826646852665)
        ·
          refine ⟨3611803077593119985139499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4815737436790826646852665 3611803077593119985139499)
          ·
            refine ⟨5417704616389679977709249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3611803077593119985139499 5417704616389679977709249)
            ·
              refine ⟨4063278462292259983281937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5417704616389679977709249 4063278462292259983281937)
              ·
                refine ⟨3047458846719194987461453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4063278462292259983281937 3047458846719194987461453)
                ·
                  refine ⟨1142797067519698120298045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3047458846719194987461453 1142797067519698120298045)
                  ·
                    refine ⟨428548900319886795111767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1142797067519698120298045 428548900319886795111767)
                    ·
                      rfl

theorem cell22_1251894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_1251894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1251894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1251894 prefixEnd_1251894 := by exact prefixLift 1251894
  have htrace : WordTrace (prefixWord ++ tailWord_1251894) baseStart_1251894 baseEnd_1251894 := by
    simpa [prefixWord, tailWord_1251894, baseEnd_1251894] using wordTrace_append hprefix tailTrace_1251894
  have hstable : (prefixWord ++ tailWord_1251894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251894).length < 2 ^ (prefixWord ++ tailWord_1251894).sum := by decide
  have hdescent : baseEnd_1251894 < baseStart_1251894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251911 : List Nat := [1, 1, 4, 1, 4, 3, 1, 3, 1, 3]
def baseStart_1251911 : Nat := 118140960795 + 1251911 * 2 ^ 59
def prefixEnd_1251911 : Nat := 4983230072969 + 3 ^ 40 * 1251911 * 2
def baseEnd_1251911 : Nat := 428554719767304417436715

theorem tailTrace_1251911 : CollatzResearch.WordTrace tailWord_1251911 prefixEnd_1251911 428554719767304417436715 := by
  unfold tailWord_1251911
  simp only [CollatzResearch.WordTrace]
  refine ⟨45660945367547731221675587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30440630245031820814450391 45660945367547731221675587)
  ·
    refine ⟨68491418051321596832513381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45660945367547731221675587 68491418051321596832513381)
    ·
      refine ⟨12842140884622799406096259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68491418051321596832513381 12842140884622799406096259)
      ·
        refine ⟨19263211326934199109144389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12842140884622799406096259 19263211326934199109144389)
        ·
          refine ⟨3611852123800162332964573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19263211326934199109144389 3611852123800162332964573)
          ·
            refine ⟨1354444546425060874861715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3611852123800162332964573 1354444546425060874861715)
            ·
              refine ⟨2031666819637591312292573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1354444546425060874861715 2031666819637591312292573)
              ·
                refine ⟨761875057364096742109715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2031666819637591312292573 761875057364096742109715)
                ·
                  refine ⟨1142812586046145113164573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 761875057364096742109715 1142812586046145113164573)
                  ·
                    refine ⟨428554719767304417436715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1142812586046145113164573 428554719767304417436715)
                    ·
                      rfl

theorem cell22_1251911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 3, 1, 3].length) (baseStart_1251911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1251911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1251911 prefixEnd_1251911 := by exact prefixLift 1251911
  have htrace : WordTrace (prefixWord ++ tailWord_1251911) baseStart_1251911 baseEnd_1251911 := by
    simpa [prefixWord, tailWord_1251911, baseEnd_1251911] using wordTrace_append hprefix tailTrace_1251911
  have hstable : (prefixWord ++ tailWord_1251911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251911).length < 2 ^ (prefixWord ++ tailWord_1251911).sum := by decide
  have hdescent : baseEnd_1251911 < baseStart_1251911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251941 : List Nat := [1, 3, 1, 3, 5, 1, 2, 1, 5]
def baseStart_1251941 : Nat := 118140960795 + 1251941 * 2 ^ 59
def prefixEnd_1251941 : Nat := 4983230072969 + 3 ^ 40 * 1251941 * 2
def baseEnd_1251941 : Nat := 142854996460131446395541

theorem tailTrace_1251941 : CollatzResearch.WordTrace tailWord_1251941 prefixEnd_1251941 142854996460131446395541 := by
  unfold tailWord_1251941
  simp only [CollatzResearch.WordTrace]
  refine ⟨45662039557439046345267677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30441359704959364230178451 45662039557439046345267677)
  ·
    refine ⟨17123264834039642379475379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45662039557439046345267677 17123264834039642379475379)
    ·
      refine ⟨25684897251059463569213069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17123264834039642379475379 25684897251059463569213069)
      ·
        refine ⟨9631836469147298838454901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25684897251059463569213069 9631836469147298838454901)
        ·
          refine ⟨902984668982559266105147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9631836469147298838454901 902984668982559266105147)
          ·
            refine ⟨1354477003473838899157721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 902984668982559266105147 1354477003473838899157721)
            ·
              refine ⟨1015857752605379174368291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1354477003473838899157721 1015857752605379174368291)
              ·
                refine ⟨1523786628908068761552437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1015857752605379174368291 1523786628908068761552437)
                ·
                  refine ⟨142854996460131446395541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1523786628908068761552437 142854996460131446395541)
                  ·
                    rfl

theorem cell22_1251941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 5].length) (baseStart_1251941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1251941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1251941 prefixEnd_1251941 := by exact prefixLift 1251941
  have htrace : WordTrace (prefixWord ++ tailWord_1251941) baseStart_1251941 baseEnd_1251941 := by
    simpa [prefixWord, tailWord_1251941, baseEnd_1251941] using wordTrace_append hprefix tailTrace_1251941
  have hstable : (prefixWord ++ tailWord_1251941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251941).length < 2 ^ (prefixWord ++ tailWord_1251941).sum := by decide
  have hdescent : baseEnd_1251941 < baseStart_1251941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251982 : List Nat := [4, 1, 1, 3, 1, 1, 1, 4, 2, 4]
def baseStart_1251982 : Nat := 118140960795 + 1251982 * 2 ^ 59
def prefixEnd_1251982 : Nat := 4983230072969 + 3 ^ 40 * 1251982 * 2
def baseEnd_1251982 : Nat := 428579024518283898911497

theorem tailTrace_1251982 : CollatzResearch.WordTrace tailWord_1251982 prefixEnd_1251982 428579024518283898911497 := by
  unfold tailWord_1251982
  simp only [CollatzResearch.WordTrace]
  refine ⟨5707941868786313793438775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30442356633527006898340133 5707941868786313793438775)
  ·
    refine ⟨8561912803179470690158163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5707941868786313793438775 8561912803179470690158163)
    ·
      refine ⟨12842869204769206035237245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8561912803179470690158163 12842869204769206035237245)
      ·
        refine ⟨4816075951788452263213967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12842869204769206035237245 4816075951788452263213967)
        ·
          refine ⟨7224113927682678394820951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4816075951788452263213967 7224113927682678394820951)
          ·
            refine ⟨10836170891524017592231427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7224113927682678394820951 10836170891524017592231427)
            ·
              refine ⟨16254256337286026388347141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10836170891524017592231427 16254256337286026388347141)
              ·
                refine ⟨3047673063241129947815089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16254256337286026388347141 3047673063241129947815089)
                ·
                  refine ⟨2285754797430847460861317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3047673063241129947815089 2285754797430847460861317)
                  ·
                    refine ⟨428579024518283898911497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2285754797430847460861317 428579024518283898911497)
                    ·
                      rfl

theorem cell22_1251982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_1251982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1251982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1251982 prefixEnd_1251982 := by exact prefixLift 1251982
  have htrace : WordTrace (prefixWord ++ tailWord_1251982) baseStart_1251982 baseEnd_1251982 := by
    simpa [prefixWord, tailWord_1251982, baseEnd_1251982] using wordTrace_append hprefix tailTrace_1251982
  have hstable : (prefixWord ++ tailWord_1251982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251982).length < 2 ^ (prefixWord ++ tailWord_1251982).sum := by decide
  have hdescent : baseEnd_1251982 < baseStart_1251982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251986 : List Nat := [3, 2, 3, 1, 2, 1, 4, 2, 4]
def baseStart_1251986 : Nat := 118140960795 + 1251986 * 2 ^ 59
def prefixEnd_1251986 : Nat := 4983230072969 + 3 ^ 40 * 1251986 * 2
def baseEnd_1251986 : Nat := 142860131266676407270495

theorem tailTrace_1251986 : CollatzResearch.WordTrace tailWord_1251986 prefixEnd_1251986 142860131266676407270495 := by
  unfold tailWord_1251986
  simp only [CollatzResearch.WordTrace]
  refine ⟨11415920210569004757663953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30442453894850679353770541 11415920210569004757663953)
  ·
    refine ⟨8561940157926753568247965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11415920210569004757663953 8561940157926753568247965)
    ·
      refine ⟨3210727559222532588092987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8561940157926753568247965 3210727559222532588092987)
      ·
        refine ⟨4816091338833798882139481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3210727559222532588092987 4816091338833798882139481)
        ·
          refine ⟨3612068504125349161604611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4816091338833798882139481 3612068504125349161604611)
          ·
            refine ⟨5418102756188023742406917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3612068504125349161604611 5418102756188023742406917)
            ·
              refine ⟨1015894266785254451701297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5418102756188023742406917 1015894266785254451701297)
              ·
                refine ⟨761920700088940838775973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1015894266785254451701297 761920700088940838775973)
                ·
                  refine ⟨142860131266676407270495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 761920700088940838775973 142860131266676407270495)
                  ·
                    rfl

theorem cell22_1251986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_1251986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1251986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1251986 prefixEnd_1251986 := by exact prefixLift 1251986
  have htrace : WordTrace (prefixWord ++ tailWord_1251986) baseStart_1251986 baseEnd_1251986 := by
    simpa [prefixWord, tailWord_1251986, baseEnd_1251986] using wordTrace_append hprefix tailTrace_1251986
  have hstable : (prefixWord ++ tailWord_1251986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251986).length < 2 ^ (prefixWord ++ tailWord_1251986).sum := by decide
  have hdescent : baseEnd_1251986 < baseStart_1251986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252025 : List Nat := [1, 2, 1, 4, 1, 1, 1, 4, 7]
def baseStart_1252025 : Nat := 118140960795 + 1252025 * 2 ^ 59
def prefixEnd_1252025 : Nat := 4983230072969 + 3 ^ 40 * 1252025 * 2
def baseEnd_1252025 : Nat := 142864581432348706695455

theorem tailTrace_1252025 : CollatzResearch.WordTrace tailWord_1252025 prefixEnd_1252025 142864581432348706695455 := by
  unfold tailWord_1252025
  simp only [CollatzResearch.WordTrace]
  refine ⟨45665103289134728691325529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30443402192756485794217019 45665103289134728691325529)
  ·
    refine ⟨34248827466851046518494147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45665103289134728691325529 34248827466851046518494147)
    ·
      refine ⟨51373241200276569777741221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34248827466851046518494147 51373241200276569777741221)
      ·
        refine ⟨9632482725051856833326479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51373241200276569777741221 9632482725051856833326479)
        ·
          refine ⟨14448724087577785249989719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9632482725051856833326479 14448724087577785249989719)
          ·
            refine ⟨21673086131366677874984579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14448724087577785249989719 21673086131366677874984579)
            ·
              refine ⟨32509629197050016812476869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21673086131366677874984579 32509629197050016812476869)
              ·
                refine ⟨6095555474446878152339413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32509629197050016812476869 6095555474446878152339413)
                ·
                  refine ⟨142864581432348706695455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6095555474446878152339413 142864581432348706695455)
                  ·
                    rfl

theorem cell22_1252025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 7].length) (baseStart_1252025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1252025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1252025 prefixEnd_1252025 := by exact prefixLift 1252025
  have htrace : WordTrace (prefixWord ++ tailWord_1252025) baseStart_1252025 baseEnd_1252025 := by
    simpa [prefixWord, tailWord_1252025, baseEnd_1252025] using wordTrace_append hprefix tailTrace_1252025
  have hstable : (prefixWord ++ tailWord_1252025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252025).length < 2 ^ (prefixWord ++ tailWord_1252025).sum := by decide
  have hdescent : baseEnd_1252025 < baseStart_1252025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252042 : List Nat := [3, 1, 2, 1, 4, 2, 1, 1, 7]
def baseStart_1252042 : Nat := 118140960795 + 1252042 * 2 ^ 59
def prefixEnd_1252042 : Nat := 4983230072969 + 3 ^ 40 * 1252042 * 2
def baseEnd_1252042 : Nat := 142866521248154580803771

theorem tailTrace_1252042 : CollatzResearch.WordTrace tailWord_1252042 prefixEnd_1252042 142866521248154580803771 := by
  unfold tailWord_1252042
  simp only [CollatzResearch.WordTrace]
  refine ⟨11416430832518285148673595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30443815553382093729796253 11416430832518285148673595)
  ·
    refine ⟨17124646248777427723010393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11416430832518285148673595 17124646248777427723010393)
    ·
      refine ⟨12843484686583070792257795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17124646248777427723010393 12843484686583070792257795)
      ·
        refine ⟨19265227029874606188386693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12843484686583070792257795 19265227029874606188386693)
        ·
          refine ⟨3612230068101488660322505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19265227029874606188386693 3612230068101488660322505)
          ·
            refine ⟨2709172551076116495241879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3612230068101488660322505 2709172551076116495241879)
            ·
              refine ⟨4063758826614174742862819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2709172551076116495241879 4063758826614174742862819)
              ·
                refine ⟨6095638239921262114294229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4063758826614174742862819 6095638239921262114294229)
                ·
                  refine ⟨142866521248154580803771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6095638239921262114294229 142866521248154580803771)
                  ·
                    rfl

theorem cell22_1252042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 7].length) (baseStart_1252042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1252042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1252042 prefixEnd_1252042 := by exact prefixLift 1252042
  have htrace : WordTrace (prefixWord ++ tailWord_1252042) baseStart_1252042 baseEnd_1252042 := by
    simpa [prefixWord, tailWord_1252042, baseEnd_1252042] using wordTrace_append hprefix tailTrace_1252042
  have hstable : (prefixWord ++ tailWord_1252042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252042).length < 2 ^ (prefixWord ++ tailWord_1252042).sum := by decide
  have hdescent : baseEnd_1252042 < baseStart_1252042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252046 : List Nat := [4, 1, 1, 1, 3, 2, 2, 4, 1, 3]
def baseStart_1252046 : Nat := 118140960795 + 1252046 * 2 ^ 59
def prefixEnd_1252046 : Nat := 4983230072969 + 3 ^ 40 * 1252046 * 2
def baseEnd_1252046 : Nat := 428600933026209065311301

theorem tailTrace_1252046 : CollatzResearch.WordTrace tailWord_1252046 prefixEnd_1252046 428600933026209065311301 := by
  unfold tailWord_1252046
  simp only [CollatzResearch.WordTrace]
  refine ⟨5708233652757331159729999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30443912814705766185226661 5708233652757331159729999)
  ·
    refine ⟨8562350479135996739594999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5708233652757331159729999 8562350479135996739594999)
    ·
      refine ⟨12843525718703995109392499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8562350479135996739594999 12843525718703995109392499)
      ·
        refine ⟨19265288578055992664088749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12843525718703995109392499 19265288578055992664088749)
        ·
          refine ⟨7224483216770997249033281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19265288578055992664088749 7224483216770997249033281)
          ·
            refine ⟨5418362412578247936774961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7224483216770997249033281 5418362412578247936774961)
            ·
              refine ⟨4063771809433685952581221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5418362412578247936774961 4063771809433685952581221)
              ·
                refine ⟨761957214268816116108979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4063771809433685952581221 761957214268816116108979)
                ·
                  refine ⟨1142935821403224174163469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 761957214268816116108979 1142935821403224174163469)
                  ·
                    refine ⟨428600933026209065311301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1142935821403224174163469 428600933026209065311301)
                    ·
                      rfl

theorem cell22_1252046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 4, 1, 3].length) (baseStart_1252046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1252046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1252046 prefixEnd_1252046 := by exact prefixLift 1252046
  have htrace : WordTrace (prefixWord ++ tailWord_1252046) baseStart_1252046 baseEnd_1252046 := by
    simpa [prefixWord, tailWord_1252046, baseEnd_1252046] using wordTrace_append hprefix tailTrace_1252046
  have hstable : (prefixWord ++ tailWord_1252046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252046).length < 2 ^ (prefixWord ++ tailWord_1252046).sum := by decide
  have hdescent : baseEnd_1252046 < baseStart_1252046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252104 : List Nat := [2, 1, 3, 2, 2, 4, 1, 1, 6]
def baseStart_1252104 : Nat := 118140960795 + 1252104 * 2 ^ 59
def prefixEnd_1252104 : Nat := 4983230072969 + 3 ^ 40 * 1252104 * 2
def baseEnd_1252104 : Nat := 142873595870505415787041

theorem tailTrace_1252104 : CollatzResearch.WordTrace tailWord_1252104 prefixEnd_1252104 142873595870505415787041 := by
  unfold tailWord_1252104
  simp only [CollatzResearch.WordTrace]
  refine ⟨22833992327924262591725683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30445323103899016788967577 22833992327924262591725683)
  ·
    refine ⟨34250988491886393887588525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22833992327924262591725683 34250988491886393887588525)
    ·
      refine ⟨12844120684457397707845697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34250988491886393887588525 12844120684457397707845697)
      ·
        refine ⟨9633090513343048280884273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12844120684457397707845697 9633090513343048280884273)
        ·
          refine ⟨7224817885007286210663205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9633090513343048280884273 7224817885007286210663205)
          ·
            refine ⟨1354653353438866164499351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7224817885007286210663205 1354653353438866164499351)
            ·
              refine ⟨2031980030158299246749027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1354653353438866164499351 2031980030158299246749027)
              ·
                refine ⟨3047970045237448870123541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2031980030158299246749027 3047970045237448870123541)
                ·
                  refine ⟨142873595870505415787041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3047970045237448870123541 142873595870505415787041)
                  ·
                    rfl

theorem cell22_1252104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 6].length) (baseStart_1252104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1252104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1252104 prefixEnd_1252104 := by exact prefixLift 1252104
  have htrace : WordTrace (prefixWord ++ tailWord_1252104) baseStart_1252104 baseEnd_1252104 := by
    simpa [prefixWord, tailWord_1252104, baseEnd_1252104] using wordTrace_append hprefix tailTrace_1252104
  have hstable : (prefixWord ++ tailWord_1252104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252104).length < 2 ^ (prefixWord ++ tailWord_1252104).sum := by decide
  have hdescent : baseEnd_1252104 < baseStart_1252104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252117 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 4, 4]
def baseStart_1252117 : Nat := 118140960795 + 1252117 * 2 ^ 59
def prefixEnd_1252117 : Nat := 4983230072969 + 3 ^ 40 * 1252117 * 2
def baseEnd_1252117 : Nat := 428625237777188546786083

theorem tailTrace_1252117 : CollatzResearch.WordTrace tailWord_1252117 prefixEnd_1252117 428625237777188546786083 := by
  unfold tailWord_1252117
  simp only [CollatzResearch.WordTrace]
  refine ⟨45668458804801428403674605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30445639203200952269116403 45668458804801428403674605)
  ·
    refine ⟨17125672051800535651377977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45668458804801428403674605 17125672051800535651377977)
    ·
      refine ⟨12844254038850401738533483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17125672051800535651377977 12844254038850401738533483)
      ·
        refine ⟨19266381058275602607800225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12844254038850401738533483 19266381058275602607800225)
        ·
          refine ⟨14449785793706701955850169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19266381058275602607800225 14449785793706701955850169)
          ·
            refine ⟨10837339345280026466887627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14449785793706701955850169 10837339345280026466887627)
            ·
              refine ⟨16256009017920039700331441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10837339345280026466887627 16256009017920039700331441)
              ·
                refine ⟨12192006763440029775248581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16256009017920039700331441 12192006763440029775248581)
                ·
                  refine ⟨2286001268145005582859109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12192006763440029775248581 2286001268145005582859109)
                  ·
                    refine ⟨428625237777188546786083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2286001268145005582859109 428625237777188546786083)
                    ·
                      rfl

theorem cell22_1252117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_1252117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1252117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1252117 prefixEnd_1252117 := by exact prefixLift 1252117
  have htrace : WordTrace (prefixWord ++ tailWord_1252117) baseStart_1252117 baseEnd_1252117 := by
    simpa [prefixWord, tailWord_1252117, baseEnd_1252117] using wordTrace_append hprefix tailTrace_1252117
  have hstable : (prefixWord ++ tailWord_1252117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252117).length < 2 ^ (prefixWord ++ tailWord_1252117).sum := by decide
  have hdescent : baseEnd_1252117 < baseStart_1252117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252192 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 1, 7]
def baseStart_1252192 : Nat := 118140960795 + 1252192 * 2 ^ 59
def prefixEnd_1252192 : Nat := 4983230072969 + 3 ^ 40 * 1252192 * 2
def baseEnd_1252192 : Nat := 428650911809913351160853

theorem tailTrace_1252192 : CollatzResearch.WordTrace tailWord_1252192 prefixEnd_1252192 428650911809913351160853 := by
  unfold tailWord_1252192
  simp only [CollatzResearch.WordTrace]
  refine ⟨22835597139764858106327415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30447462853019810808436553 22835597139764858106327415)
  ·
    refine ⟨34253395709647287159491123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22835597139764858106327415 34253395709647287159491123)
    ·
      refine ⟨51380093564470930739236685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34253395709647287159491123 51380093564470930739236685)
      ·
        refine ⟨19267535086676599027213757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51380093564470930739236685 19267535086676599027213757)
        ·
          refine ⟨7225325657503724635205159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19267535086676599027213757 7225325657503724635205159)
          ·
            refine ⟨10837988486255586952807739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7225325657503724635205159 10837988486255586952807739)
            ·
              refine ⟨16256982729383380429211609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10837988486255586952807739 16256982729383380429211609)
              ·
                refine ⟨12192737047037535321908707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16256982729383380429211609 12192737047037535321908707)
                ·
                  refine ⟨18289105570556302982863061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12192737047037535321908707 18289105570556302982863061)
                  ·
                    refine ⟨428650911809913351160853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18289105570556302982863061 428650911809913351160853)
                    ·
                      rfl

theorem cell22_1252192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 1, 7].length) (baseStart_1252192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1252192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1252192 prefixEnd_1252192 := by exact prefixLift 1252192
  have htrace : WordTrace (prefixWord ++ tailWord_1252192) baseStart_1252192 baseEnd_1252192 := by
    simpa [prefixWord, tailWord_1252192, baseEnd_1252192] using wordTrace_append hprefix tailTrace_1252192
  have hstable : (prefixWord ++ tailWord_1252192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252192).length < 2 ^ (prefixWord ++ tailWord_1252192).sum := by decide
  have hdescent : baseEnd_1252192 < baseStart_1252192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252256 : List Nat := [2, 1, 1, 4, 1, 1, 5, 3, 4]
def baseStart_1252256 : Nat := 118140960795 + 1252256 * 2 ^ 59
def prefixEnd_1252256 : Nat := 4983230072969 + 3 ^ 40 * 1252256 * 2
def baseEnd_1252256 : Nat := 142890940105946172520219

theorem tailTrace_1252256 : CollatzResearch.WordTrace tailWord_1252256 prefixEnd_1252256 142890940105946172520219 := by
  unfold tailWord_1252256
  simp only [CollatzResearch.WordTrace]
  refine ⟨22836764275648927571492311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30449019034198570095323081 22836764275648927571492311)
  ·
    refine ⟨34255146413473391357238467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22836764275648927571492311 34255146413473391357238467)
    ·
      refine ⟨51382719620210087035857701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34255146413473391357238467 51382719620210087035857701)
      ·
        refine ⟨9634259928789391319223319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51382719620210087035857701 9634259928789391319223319)
        ·
          refine ⟨14451389893184086978834979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9634259928789391319223319 14451389893184086978834979)
          ·
            refine ⟨21677084839776130468252469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14451389893184086978834979 21677084839776130468252469)
            ·
              refine ⟨2032226703729012231398669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21677084839776130468252469 2032226703729012231398669)
              ·
                refine ⟨762085013898379586774501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2032226703729012231398669 762085013898379586774501)
                ·
                  refine ⟨142890940105946172520219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 762085013898379586774501 142890940105946172520219)
                  ·
                    rfl

theorem cell22_1252256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 3, 4].length) (baseStart_1252256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1252256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1252256 prefixEnd_1252256 := by exact prefixLift 1252256
  have htrace : WordTrace (prefixWord ++ tailWord_1252256) baseStart_1252256 baseEnd_1252256 := by
    simpa [prefixWord, tailWord_1252256, baseEnd_1252256] using wordTrace_append hprefix tailTrace_1252256
  have hstable : (prefixWord ++ tailWord_1252256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252256).length < 2 ^ (prefixWord ++ tailWord_1252256).sum := by decide
  have hdescent : baseEnd_1252256 < baseStart_1252256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252273 : List Nat := [1, 2, 2, 4, 4, 1, 1, 1, 6]
def baseStart_1252273 : Nat := 118140960795 + 1252273 * 2 ^ 59
def prefixEnd_1252273 : Nat := 4983230072969 + 3 ^ 40 * 1252273 * 2
def baseEnd_1252273 : Nat := 142892879921752046628535

theorem tailTrace_1252273 : CollatzResearch.WordTrace tailWord_1252273 prefixEnd_1252273 142892879921752046628535 := by
  unfold tailWord_1252273
  simp only [CollatzResearch.WordTrace]
  refine ⟨45674148592236267046353473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30449432394824178030902315 45674148592236267046353473)
  ·
    refine ⟨34255611444177200284765105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45674148592236267046353473 34255611444177200284765105)
    ·
      refine ⟨25691708583132900213573829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34255611444177200284765105 25691708583132900213573829)
      ·
        refine ⟨4817195359337418790045093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25691708583132900213573829 4817195359337418790045093)
        ·
          refine ⟨903224129875766023133455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4817195359337418790045093 903224129875766023133455)
          ·
            refine ⟨1354836194813649034700183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 903224129875766023133455 1354836194813649034700183)
            ·
              refine ⟨2032254292220473552050275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1354836194813649034700183 2032254292220473552050275)
              ·
                refine ⟨3048381438330710328075413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2032254292220473552050275 3048381438330710328075413)
                ·
                  refine ⟨142892879921752046628535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3048381438330710328075413 142892879921752046628535)
                  ·
                    rfl

theorem cell22_1252273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 6].length) (baseStart_1252273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1252273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1252273 prefixEnd_1252273 := by exact prefixLift 1252273
  have htrace : WordTrace (prefixWord ++ tailWord_1252273) baseStart_1252273 baseEnd_1252273 := by
    simpa [prefixWord, tailWord_1252273, baseEnd_1252273] using wordTrace_append hprefix tailTrace_1252273
  have hstable : (prefixWord ++ tailWord_1252273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252273).length < 2 ^ (prefixWord ++ tailWord_1252273).sum := by decide
  have hdescent : baseEnd_1252273 < baseStart_1252273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252288 : List Nat := [2, 1, 1, 2, 3, 3, 4, 1, 2, 3]
def baseStart_1252288 : Nat := 118140960795 + 1252288 * 2 ^ 59
def prefixEnd_1252288 : Nat := 4983230072969 + 3 ^ 40 * 1252288 * 2
def baseEnd_1252288 : Nat := 428683774571801100760559

theorem tailTrace_1252288 : CollatzResearch.WordTrace tailWord_1252288 prefixEnd_1252288 428683774571801100760559 := by
  unfold tailWord_1252288
  simp only [CollatzResearch.WordTrace]
  refine ⟨22837347843590962304074759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30449797124787949738766345 22837347843590962304074759)
  ·
    refine ⟨34256021765386443456112139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22837347843590962304074759 34256021765386443456112139)
    ·
      refine ⟨51384032648079665184168209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34256021765386443456112139 51384032648079665184168209)
      ·
        refine ⟨38538024486059748888126157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51384032648079665184168209 38538024486059748888126157)
        ·
          refine ⟨14451759182272405833047309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38538024486059748888126157 14451759182272405833047309)
          ·
            refine ⟨5419409693352152187392741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14451759182272405833047309 5419409693352152187392741)
            ·
              refine ⟨1016139317503528535136139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5419409693352152187392741 1016139317503528535136139)
              ·
                refine ⟨1524208976255292802704209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1016139317503528535136139 1524208976255292802704209)
                ·
                  refine ⟨1143156732191469602028157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1524208976255292802704209 1143156732191469602028157)
                  ·
                    refine ⟨428683774571801100760559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1143156732191469602028157 428683774571801100760559)
                    ·
                      rfl

theorem cell22_1252288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 2, 3].length) (baseStart_1252288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1252288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1252288 prefixEnd_1252288 := by exact prefixLift 1252288
  have htrace : WordTrace (prefixWord ++ tailWord_1252288) baseStart_1252288 baseEnd_1252288 := by
    simpa [prefixWord, tailWord_1252288, baseEnd_1252288] using wordTrace_append hprefix tailTrace_1252288
  have hstable : (prefixWord ++ tailWord_1252288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252288).length < 2 ^ (prefixWord ++ tailWord_1252288).sum := by decide
  have hdescent : baseEnd_1252288 < baseStart_1252288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252292 : List Nat := [2, 3, 3, 3, 2, 1, 1, 2, 1, 4]
def baseStart_1252292 : Nat := 118140960795 + 1252292 * 2 ^ 59
def prefixEnd_1252292 : Nat := 4983230072969 + 3 ^ 40 * 1252292 * 2
def baseEnd_1252292 : Nat := 428685143853546423660547

theorem tailTrace_1252292 : CollatzResearch.WordTrace tailWord_1252292 prefixEnd_1252292 428685143853546423660547 := by
  unfold tailWord_1252292
  simp only [CollatzResearch.WordTrace]
  refine ⟨22837420789583716645647565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30449894386111622194196753 22837420789583716645647565)
  ·
    refine ⟨8564032796093893742117837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22837420789583716645647565 8564032796093893742117837)
    ·
      refine ⟨3211512298535210153294189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8564032796093893742117837 3211512298535210153294189)
      ·
        refine ⟨1204317111950703807485321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3211512298535210153294189 1204317111950703807485321)
        ·
          refine ⟨903237833963027855613991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1204317111950703807485321 903237833963027855613991)
          ·
            refine ⟨1354856750944541783420987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 903237833963027855613991 1354856750944541783420987)
            ·
              refine ⟨2032285126416812675131481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1354856750944541783420987 2032285126416812675131481)
              ·
                refine ⟨1524213844812609506348611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2032285126416812675131481 1524213844812609506348611)
                ·
                  refine ⟨2286320767218914259522917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1524213844812609506348611 2286320767218914259522917)
                  ·
                    refine ⟨428685143853546423660547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2286320767218914259522917 428685143853546423660547)
                    ·
                      rfl

theorem cell22_1252292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_1252292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1252292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1252292 prefixEnd_1252292 := by exact prefixLift 1252292
  have htrace : WordTrace (prefixWord ++ tailWord_1252292) baseStart_1252292 baseEnd_1252292 := by
    simpa [prefixWord, tailWord_1252292, baseEnd_1252292] using wordTrace_append hprefix tailTrace_1252292
  have hstable : (prefixWord ++ tailWord_1252292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252292).length < 2 ^ (prefixWord ++ tailWord_1252292).sum := by decide
  have hdescent : baseEnd_1252292 < baseStart_1252292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252350 : List Nat := [4, 2, 2, 2, 2, 1, 1, 2, 3, 3]
def baseStart_1252350 : Nat := 118140960795 + 1252350 * 2 ^ 59
def prefixEnd_1252350 : Nat := 4983230072969 + 3 ^ 40 * 1252350 * 2
def baseEnd_1252350 : Nat := 428704998438853605710369

theorem tailTrace_1252350 : CollatzResearch.WordTrace tailWord_1252350 prefixEnd_1252350 428704998438853605710369 := by
  unfold tailWord_1252350
  simp only [CollatzResearch.WordTrace]
  refine ⟨5709619626619663649613313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30451304675304872797937669 5709619626619663649613313)
  ·
    refine ⟨4282214719964747737209985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5709619626619663649613313 4282214719964747737209985)
    ·
      refine ⟨3211661039973560802907489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4282214719964747737209985 3211661039973560802907489)
      ·
        refine ⟨2408745779980170602180617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3211661039973560802907489 2408745779980170602180617)
        ·
          refine ⟨1806559334985127951635463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2408745779980170602180617 1806559334985127951635463)
          ·
            refine ⟨2709839002477691927453195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1806559334985127951635463 2709839002477691927453195)
            ·
              refine ⟨4064758503716537891179793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2709839002477691927453195 4064758503716537891179793)
              ·
                refine ⟨3048568877787403418384845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4064758503716537891179793 3048568877787403418384845)
                ·
                  refine ⟨1143213329170276281894317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3048568877787403418384845 1143213329170276281894317)
                  ·
                    refine ⟨428704998438853605710369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1143213329170276281894317 428704998438853605710369)
                    ·
                      rfl

theorem cell22_1252350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_1252350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1252350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1252350 prefixEnd_1252350 := by exact prefixLift 1252350
  have htrace : WordTrace (prefixWord ++ tailWord_1252350) baseStart_1252350 baseEnd_1252350 := by
    simpa [prefixWord, tailWord_1252350, baseEnd_1252350] using wordTrace_append hprefix tailTrace_1252350
  have hstable : (prefixWord ++ tailWord_1252350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252350).length < 2 ^ (prefixWord ++ tailWord_1252350).sum := by decide
  have hdescent : baseEnd_1252350 < baseStart_1252350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252380 : List Nat := [2, 2, 3, 1, 5, 1, 1, 2, 5]
def baseStart_1252380 : Nat := 118140960795 + 1252380 * 2 ^ 59
def prefixEnd_1252380 : Nat := 4983230072969 + 3 ^ 40 * 1252380 * 2
def baseEnd_1252380 : Nat := 142905089350647842486759

theorem tailTrace_1252380 : CollatzResearch.WordTrace tailWord_1252380 prefixEnd_1252380 142905089350647842486759 := by
  unfold tailWord_1252380
  simp only [CollatzResearch.WordTrace]
  refine ⟨22839025601424312160249297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30452034135232416213665729 22839025601424312160249297)
  ·
    refine ⟨17129269201068234120186973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22839025601424312160249297 17129269201068234120186973)
    ·
      refine ⟨6423475950400587795070115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17129269201068234120186973 6423475950400587795070115)
      ·
        refine ⟨9635213925600881692605173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6423475950400587795070115 9635213925600881692605173)
        ·
          refine ⟨903301305525082658681735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9635213925600881692605173 903301305525082658681735)
          ·
            refine ⟨1354951958287623988022603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 903301305525082658681735 1354951958287623988022603)
            ·
              refine ⟨2032427937431435982033905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1354951958287623988022603 2032427937431435982033905)
              ·
                refine ⟨1524320953073576986525429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2032427937431435982033905 1524320953073576986525429)
                ·
                  refine ⟨142905089350647842486759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1524320953073576986525429 142905089350647842486759)
                  ·
                    rfl

theorem cell22_1252380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 5].length) (baseStart_1252380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1252380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1252380 prefixEnd_1252380 := by exact prefixLift 1252380
  have htrace : WordTrace (prefixWord ++ tailWord_1252380) baseStart_1252380 baseEnd_1252380 := by
    simpa [prefixWord, tailWord_1252380, baseEnd_1252380] using wordTrace_append hprefix tailTrace_1252380
  have hstable : (prefixWord ++ tailWord_1252380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252380).length < 2 ^ (prefixWord ++ tailWord_1252380).sum := by decide
  have hdescent : baseEnd_1252380 < baseStart_1252380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252419 : List Nat := [1, 1, 1, 3, 1, 2, 5, 8]
def baseStart_1252419 : Nat := 118140960795 + 1252419 * 2 ^ 59
def prefixEnd_1252419 : Nat := 4983230072969 + 3 ^ 40 * 1252419 * 2
def baseEnd_1252419 : Nat := 47636513172106713970573

theorem tailTrace_1252419 : CollatzResearch.WordTrace tailWord_1252419 prefixEnd_1252419 47636513172106713970573 := by
  unfold tailWord_1252419
  simp only [CollatzResearch.WordTrace]
  refine ⟨45679473649707333981168311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30452982433138222654112207 45679473649707333981168311)
  ·
    refine ⟨68519210474561000971752467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45679473649707333981168311 68519210474561000971752467)
    ·
      refine ⟨102778815711841501457628701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68519210474561000971752467 102778815711841501457628701)
      ·
        refine ⟨38542055891940563046610763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102778815711841501457628701 38542055891940563046610763)
        ·
          refine ⟨57813083837910844569916145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38542055891940563046610763 57813083837910844569916145)
          ·
            refine ⟨43359812878433133427437109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57813083837910844569916145 43359812878433133427437109)
            ·
              refine ⟨4064982457353106258822229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43359812878433133427437109 4064982457353106258822229)
              ·
                refine ⟨47636513172106713970573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4064982457353106258822229 47636513172106713970573)
                ·
                  rfl

theorem cell22_1252419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 8].length) (baseStart_1252419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1252419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1252419 prefixEnd_1252419 := by exact prefixLift 1252419
  have htrace : WordTrace (prefixWord ++ tailWord_1252419) baseStart_1252419 baseEnd_1252419 := by
    simpa [prefixWord, tailWord_1252419, baseEnd_1252419] using wordTrace_append hprefix tailTrace_1252419
  have hstable : (prefixWord ++ tailWord_1252419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252419).length < 2 ^ (prefixWord ++ tailWord_1252419).sum := by decide
  have hdescent : baseEnd_1252419 < baseStart_1252419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252498 : List Nat := [3, 2, 3, 1, 1, 2, 1, 4, 5]
def baseStart_1252498 : Nat := 118140960795 + 1252498 * 2 ^ 59
def prefixEnd_1252498 : Nat := 4983230072969 + 3 ^ 40 * 1252498 * 2
def baseEnd_1252498 : Nat := 142918553954476851003305

theorem tailTrace_1252498 : CollatzResearch.WordTrace tailWord_1252498 prefixEnd_1252498 142918553954476851003305 := by
  unfold tailWord_1252498
  simp only [CollatzResearch.WordTrace]
  refine ⟨11420588754105282618323537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30454903344280753648862765 11420588754105282618323537)
  ·
    refine ⟨8565441565578961963742653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11420588754105282618323537 8565441565578961963742653)
    ·
      refine ⟨3212040587092110736403495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8565441565578961963742653 3212040587092110736403495)
      ·
        refine ⟨4818060880638166104605243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3212040587092110736403495 4818060880638166104605243)
        ·
          refine ⟨7227091320957249156907865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4818060880638166104605243 7227091320957249156907865)
          ·
            refine ⟨5420318490717936867680899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7227091320957249156907865 5420318490717936867680899)
            ·
              refine ⟨8130477736076905301521349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5420318490717936867680899 8130477736076905301521349)
              ·
                refine ⟨1524464575514419744035253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8130477736076905301521349 1524464575514419744035253)
                ·
                  refine ⟨142918553954476851003305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1524464575514419744035253 142918553954476851003305)
                  ·
                    rfl

theorem cell22_1252498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_1252498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1252498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1252498 prefixEnd_1252498 := by exact prefixLift 1252498
  have htrace : WordTrace (prefixWord ++ tailWord_1252498) baseStart_1252498 baseEnd_1252498 := by
    simpa [prefixWord, tailWord_1252498, baseEnd_1252498] using wordTrace_append hprefix tailTrace_1252498
  have hstable : (prefixWord ++ tailWord_1252498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252498).length < 2 ^ (prefixWord ++ tailWord_1252498).sum := by decide
  have hdescent : baseEnd_1252498 < baseStart_1252498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252543 : List Nat := [1, 1, 2, 2, 2, 2, 3, 5, 4]
def baseStart_1252543 : Nat := 118140960795 + 1252543 * 2 ^ 59
def prefixEnd_1252543 : Nat := 4983230072969 + 3 ^ 40 * 1252543 * 2
def baseEnd_1252543 : Nat := 142923688761021811878259

theorem tailTrace_1252543 : CollatzResearch.WordTrace tailWord_1252543 prefixEnd_1252543 142923688761021811878259 := by
  unfold tailWord_1252543
  simp only [CollatzResearch.WordTrace]
  refine ⟨45683996301258103158682283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30455997534172068772454855 45683996301258103158682283)
  ·
    refine ⟨68525994451887154738023425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45683996301258103158682283 68525994451887154738023425)
    ·
      refine ⟨51394495838915366053517569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68525994451887154738023425 51394495838915366053517569)
      ·
        refine ⟨38545871879186524540138177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51394495838915366053517569 38545871879186524540138177)
        ·
          refine ⟨28909403909389893405103633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38545871879186524540138177 28909403909389893405103633)
          ·
            refine ⟨21682052932042420053827725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28909403909389893405103633 21682052932042420053827725)
            ·
              refine ⟨8130769849515907520185397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21682052932042420053827725 8130769849515907520185397)
              ·
                refine ⟨762259673392116330017381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8130769849515907520185397 762259673392116330017381)
                ·
                  refine ⟨142923688761021811878259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 762259673392116330017381 142923688761021811878259)
                  ·
                    rfl

theorem cell22_1252543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5, 4].length) (baseStart_1252543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1252543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1252543 prefixEnd_1252543 := by exact prefixLift 1252543
  have htrace : WordTrace (prefixWord ++ tailWord_1252543) baseStart_1252543 baseEnd_1252543 := by
    simpa [prefixWord, tailWord_1252543, baseEnd_1252543] using wordTrace_append hprefix tailTrace_1252543
  have hstable : (prefixWord ++ tailWord_1252543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252543).length < 2 ^ (prefixWord ++ tailWord_1252543).sum := by decide
  have hdescent : baseEnd_1252543 < baseStart_1252543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252588 : List Nat := [2, 2, 1, 1, 2, 4, 4, 6]
def baseStart_1252588 : Nat := 118140960795 + 1252588 * 2 ^ 59
def prefixEnd_1252588 : Nat := 4983230072969 + 3 ^ 40 * 1252588 * 2
def baseEnd_1252588 : Nat := 47642941189188924251071

theorem tailTrace_1252588 : CollatzResearch.WordTrace tailWord_1252588 prefixEnd_1252588 47642941189188924251071 := by
  unfold tailWord_1252588
  simp only [CollatzResearch.WordTrace]
  refine ⟨22842818793047537922035209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30457091724063383896046945 22842818793047537922035209)
  ·
    refine ⟨17132114094785653441526407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22842818793047537922035209 17132114094785653441526407)
    ·
      refine ⟨25698171142178480162289611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17132114094785653441526407 25698171142178480162289611)
      ·
        refine ⟨38547256713267720243434417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25698171142178480162289611 38547256713267720243434417)
        ·
          refine ⟨28910442534950790182575813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38547256713267720243434417 28910442534950790182575813)
          ·
            refine ⟨5420707975303273159232965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28910442534950790182575813 5420707975303273159232965)
            ·
              refine ⟨1016382745369363717356181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5420707975303273159232965 1016382745369363717356181)
              ·
                refine ⟨47642941189188924251071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1016382745369363717356181 47642941189188924251071)
                ·
                  rfl

theorem cell22_1252588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 6].length) (baseStart_1252588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1252588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1252588 prefixEnd_1252588 := by exact prefixLift 1252588
  have htrace : WordTrace (prefixWord ++ tailWord_1252588) baseStart_1252588 baseEnd_1252588 := by
    simpa [prefixWord, tailWord_1252588, baseEnd_1252588] using wordTrace_append hprefix tailTrace_1252588
  have hstable : (prefixWord ++ tailWord_1252588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252588).length < 2 ^ (prefixWord ++ tailWord_1252588).sum := by decide
  have hdescent : baseEnd_1252588 < baseStart_1252588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252594 : List Nat := [3, 2, 1, 3, 4, 1, 1, 3, 4]
def baseStart_1252594 : Nat := 118140960795 + 1252594 * 2 ^ 59
def prefixEnd_1252594 : Nat := 4983230072969 + 3 ^ 40 * 1252594 * 2
def baseEnd_1252594 : Nat := 142929508208439434203207

theorem tailTrace_1252594 : CollatzResearch.WordTrace tailWord_1252594 prefixEnd_1252594 142929508208439434203207 := by
  unfold tailWord_1252594
  simp only [CollatzResearch.WordTrace]
  refine ⟨11421464106018334717197209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30457237616048892579192557 11421464106018334717197209)
  ·
    refine ⟨8566098079513751037897907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11421464106018334717197209 8566098079513751037897907)
    ·
      refine ⟨12849147119270626556846861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8566098079513751037897907 12849147119270626556846861)
      ·
        refine ⟨4818430169726484958817573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12849147119270626556846861 4818430169726484958817573)
        ·
          refine ⟨903455656823715929778295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4818430169726484958817573 903455656823715929778295)
          ·
            refine ⟨1355183485235573894667443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 903455656823715929778295 1355183485235573894667443)
            ·
              refine ⟨2032775227853360842001165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1355183485235573894667443 2032775227853360842001165)
              ·
                refine ⟨762290710445010315750437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2032775227853360842001165 762290710445010315750437)
                ·
                  refine ⟨142929508208439434203207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 762290710445010315750437 142929508208439434203207)
                  ·
                    rfl

theorem cell22_1252594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_1252594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1252594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1252594 prefixEnd_1252594 := by exact prefixLift 1252594
  have htrace : WordTrace (prefixWord ++ tailWord_1252594) baseStart_1252594 baseEnd_1252594 := by
    simpa [prefixWord, tailWord_1252594, baseEnd_1252594] using wordTrace_append hprefix tailTrace_1252594
  have hstable : (prefixWord ++ tailWord_1252594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252594).length < 2 ^ (prefixWord ++ tailWord_1252594).sum := by decide
  have hdescent : baseEnd_1252594 < baseStart_1252594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252620 : List Nat := [2, 2, 1, 2, 2, 3, 3, 1, 3, 3]
def baseStart_1252620 : Nat := 118140960795 + 1252620 * 2 ^ 59
def prefixEnd_1252620 : Nat := 4983230072969 + 3 ^ 40 * 1252620 * 2
def baseEnd_1252620 : Nat := 428797424956662901459541

theorem tailTrace_1252620 : CollatzResearch.WordTrace tailWord_1252620 prefixEnd_1252620 428797424956662901459541 := by
  unfold tailWord_1252620
  simp only [CollatzResearch.WordTrace]
  refine ⟨22843402360989572654617657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30457869814652763539490209 22843402360989572654617657)
  ·
    refine ⟨17132551770742179490963243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22843402360989572654617657 17132551770742179490963243)
    ·
      refine ⟨25698827656113269236444865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17132551770742179490963243 25698827656113269236444865)
      ·
        refine ⟨19274120742084951927333649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25698827656113269236444865 19274120742084951927333649)
        ·
          refine ⟨14455590556563713945500237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19274120742084951927333649 14455590556563713945500237)
          ·
            refine ⟨5420846458711392729562589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14455590556563713945500237 5420846458711392729562589)
            ·
              refine ⟨2032817422016772273585971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5420846458711392729562589 2032817422016772273585971)
              ·
                refine ⟨3049226133025158410378957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2032817422016772273585971 3049226133025158410378957)
                ·
                  refine ⟨1143459799884434403892109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3049226133025158410378957 1143459799884434403892109)
                  ·
                    refine ⟨428797424956662901459541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1143459799884434403892109 428797424956662901459541)
                    ·
                      rfl

theorem cell22_1252620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 3, 3].length) (baseStart_1252620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1252620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1252620 prefixEnd_1252620 := by exact prefixLift 1252620
  have htrace : WordTrace (prefixWord ++ tailWord_1252620) baseStart_1252620 baseEnd_1252620 := by
    simpa [prefixWord, tailWord_1252620, baseEnd_1252620] using wordTrace_append hprefix tailTrace_1252620
  have hstable : (prefixWord ++ tailWord_1252620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252620).length < 2 ^ (prefixWord ++ tailWord_1252620).sum := by decide
  have hdescent : baseEnd_1252620 < baseStart_1252620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252744 : List Nat := [2, 1, 3, 3, 1, 3, 3, 1, 2, 3]
def baseStart_1252744 : Nat := 118140960795 + 1252744 * 2 ^ 59
def prefixEnd_1252744 : Nat := 4983230072969 + 3 ^ 40 * 1252744 * 2
def baseEnd_1252744 : Nat := 428839872690767911359161

theorem tailTrace_1252744 : CollatzResearch.WordTrace tailWord_1252744 prefixEnd_1252744 428839872690767911359161 := by
  unfold tailWord_1252744
  simp only [CollatzResearch.WordTrace]
  refine ⟨22845663686764957243374643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30460884915686609657832857 22845663686764957243374643)
  ·
    refine ⟨34268495530147435865061965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22845663686764957243374643 34268495530147435865061965)
    ·
      refine ⟨12850685823805288449398237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34268495530147435865061965 12850685823805288449398237)
      ·
        refine ⟨4819007183926983168524339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12850685823805288449398237 4819007183926983168524339)
        ·
          refine ⟨7228510775890474752786509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4819007183926983168524339 7228510775890474752786509)
          ·
            refine ⟨2710691540958928032294941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7228510775890474752786509 2710691540958928032294941)
            ·
              refine ⟨1016509327859598012110603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2710691540958928032294941 1016509327859598012110603)
              ·
                refine ⟨1524763991789397018165905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1016509327859598012110603 1524763991789397018165905)
                ·
                  refine ⟨1143572993842047763624429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1524763991789397018165905 1143572993842047763624429)
                  ·
                    refine ⟨428839872690767911359161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1143572993842047763624429 428839872690767911359161)
                    ·
                      rfl

theorem cell22_1252744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_1252744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1252744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1252744 prefixEnd_1252744 := by exact prefixLift 1252744
  have htrace : WordTrace (prefixWord ++ tailWord_1252744) baseStart_1252744 baseEnd_1252744 := by
    simpa [prefixWord, tailWord_1252744, baseEnd_1252744] using wordTrace_append hprefix tailTrace_1252744
  have hstable : (prefixWord ++ tailWord_1252744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252744).length < 2 ^ (prefixWord ++ tailWord_1252744).sum := by decide
  have hdescent : baseEnd_1252744 < baseStart_1252744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252768 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 9]
def baseStart_1252768 : Nat := 118140960795 + 1252768 * 2 ^ 59
def prefixEnd_1252768 : Nat := 4983230072969 + 3 ^ 40 * 1252768 * 2
def baseEnd_1252768 : Nat := 142949362793746616253029

theorem tailTrace_1252768 : CollatzResearch.WordTrace tailWord_1252768 prefixEnd_1252768 142949362793746616253029 := by
  unfold tailWord_1252768
  simp only [CollatzResearch.WordTrace]
  refine ⟨22846101362721483292811479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30461468483628644390415305 22846101362721483292811479)
  ·
    refine ⟨34269152044082224939217219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22846101362721483292811479 34269152044082224939217219)
    ·
      refine ⟨51403728066123337408825829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34269152044082224939217219 51403728066123337408825829)
      ·
        refine ⟨9638199012398125764154843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51403728066123337408825829 9638199012398125764154843)
        ·
          refine ⟨14457298518597188646232265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9638199012398125764154843 14457298518597188646232265)
          ·
            refine ⟨10842973888947891484674199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14457298518597188646232265 10842973888947891484674199)
            ·
              refine ⟨16264460833421837227011299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10842973888947891484674199 16264460833421837227011299)
              ·
                refine ⟨24396691250132755840516949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16264460833421837227011299 24396691250132755840516949)
                ·
                  refine ⟨142949362793746616253029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 24396691250132755840516949 142949362793746616253029)
                  ·
                    rfl

theorem cell22_1252768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 9].length) (baseStart_1252768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1252768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1252768 prefixEnd_1252768 := by exact prefixLift 1252768
  have htrace : WordTrace (prefixWord ++ tailWord_1252768) baseStart_1252768 baseEnd_1252768 := by
    simpa [prefixWord, tailWord_1252768, baseEnd_1252768] using wordTrace_append hprefix tailTrace_1252768
  have hstable : (prefixWord ++ tailWord_1252768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252768).length < 2 ^ (prefixWord ++ tailWord_1252768).sum := by decide
  have hdescent : baseEnd_1252768 < baseStart_1252768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252783 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 4, 5]
def baseStart_1252783 : Nat := 118140960795 + 1252783 * 2 ^ 59
def prefixEnd_1252783 : Nat := 4983230072969 + 3 ^ 40 * 1252783 * 2
def baseEnd_1252783 : Nat := 428853223187784809634041

theorem tailTrace_1252783 : CollatzResearch.WordTrace tailWord_1252783 prefixEnd_1252783 428853223187784809634041 := by
  unfold tailWord_1252783
  simp only [CollatzResearch.WordTrace]
  refine ⟨45692749820388624147419003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30461833213592416098279335 45692749820388624147419003)
  ·
    refine ⟨68539124730582936221128505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45692749820388624147419003 68539124730582936221128505)
    ·
      refine ⟨51404343547937202165846379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68539124730582936221128505 51404343547937202165846379)
      ·
        refine ⟨77106515321905803248769569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51404343547937202165846379 77106515321905803248769569)
        ·
          refine ⟨57829886491429352436577177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77106515321905803248769569 57829886491429352436577177)
          ·
            refine ⟨43372414868572014327432883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57829886491429352436577177 43372414868572014327432883)
            ·
              refine ⟨65058622302858021491149325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43372414868572014327432883 65058622302858021491149325)
              ·
                refine ⟨24396983363571758059180997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65058622302858021491149325 24396983363571758059180997)
                ·
                  refine ⟨4574434380669704636096437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24396983363571758059180997 4574434380669704636096437)
                  ·
                    refine ⟨428853223187784809634041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4574434380669704636096437 428853223187784809634041)
                    ·
                      rfl

theorem cell22_1252783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 5].length) (baseStart_1252783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1252783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1252783 prefixEnd_1252783 := by exact prefixLift 1252783
  have htrace : WordTrace (prefixWord ++ tailWord_1252783) baseStart_1252783 baseEnd_1252783 := by
    simpa [prefixWord, tailWord_1252783, baseEnd_1252783] using wordTrace_append hprefix tailTrace_1252783
  have hstable : (prefixWord ++ tailWord_1252783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252783).length < 2 ^ (prefixWord ++ tailWord_1252783).sum := by decide
  have hdescent : baseEnd_1252783 < baseStart_1252783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252785 : List Nat := [1, 2, 2, 4, 1, 1, 2, 4, 5]
def baseStart_1252785 : Nat := 118140960795 + 1252785 * 2 ^ 59
def prefixEnd_1252785 : Nat := 4983230072969 + 3 ^ 40 * 1252785 * 2
def baseEnd_1252785 : Nat := 142951302609552490361345

theorem tailTrace_1252785 : CollatzResearch.WordTrace tailWord_1252785 prefixEnd_1252785 142951302609552490361345 := by
  unfold tailWord_1252785
  simp only [CollatzResearch.WordTrace]
  refine ⟨45692822766381378488991809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30461881844254252325994539 45692822766381378488991809)
  ·
    refine ⟨34269617074786033866743857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45692822766381378488991809 34269617074786033866743857)
    ·
      refine ⟨25702212806089525400057893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34269617074786033866743857 25702212806089525400057893)
      ·
        refine ⟨4819164901141786012510855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25702212806089525400057893 4819164901141786012510855)
        ·
          refine ⟨7228747351712679018766283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4819164901141786012510855 7228747351712679018766283)
          ·
            refine ⟨10843121027569018528149425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7228747351712679018766283 10843121027569018528149425)
            ·
              refine ⟨8132340770676763896112069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10843121027569018528149425 8132340770676763896112069)
              ·
                refine ⟨1524813894501893230521013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8132340770676763896112069 1524813894501893230521013)
                ·
                  refine ⟨142951302609552490361345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1524813894501893230521013 142951302609552490361345)
                  ·
                    rfl

theorem cell22_1252785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 5].length) (baseStart_1252785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1252785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1252785 prefixEnd_1252785 := by exact prefixLift 1252785
  have htrace : WordTrace (prefixWord ++ tailWord_1252785) baseStart_1252785 baseEnd_1252785 := by
    simpa [prefixWord, tailWord_1252785, baseEnd_1252785] using wordTrace_append hprefix tailTrace_1252785
  have hstable : (prefixWord ++ tailWord_1252785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252785).length < 2 ^ (prefixWord ++ tailWord_1252785).sum := by decide
  have hdescent : baseEnd_1252785 < baseStart_1252785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252789 : List Nat := [1, 3, 3, 2, 2, 3, 1, 1, 3, 3]
def baseStart_1252789 : Nat := 118140960795 + 1252789 * 2 ^ 59
def prefixEnd_1252789 : Nat := 4983230072969 + 3 ^ 40 * 1252789 * 2
def baseEnd_1252789 : Nat := 428855277110402793984023

theorem tailTrace_1252789 : CollatzResearch.WordTrace tailWord_1252789 prefixEnd_1252789 428855277110402793984023 := by
  unfold tailWord_1252789
  simp only [CollatzResearch.WordTrace]
  refine ⟨45692968658366887172137421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30461979105577924781424947 45692968658366887172137421)
  ·
    refine ⟨17134863246887582689551533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45692968658366887172137421 17134863246887582689551533)
    ·
      refine ⟨6425573717582843508581825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17134863246887582689551533 6425573717582843508581825)
      ·
        refine ⟨4819180288187132631436369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6425573717582843508581825 4819180288187132631436369)
        ·
          refine ⟨3614385216140349473577277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4819180288187132631436369 3614385216140349473577277)
          ·
            refine ⟨1355394456052631052591479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3614385216140349473577277 1355394456052631052591479)
            ·
              refine ⟨2033091684078946578887219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1355394456052631052591479 2033091684078946578887219)
              ·
                refine ⟨3049637526118419868330829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2033091684078946578887219 3049637526118419868330829)
                ·
                  refine ⟨1143614072294407450624061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3049637526118419868330829 1143614072294407450624061)
                  ·
                    refine ⟨428855277110402793984023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1143614072294407450624061 428855277110402793984023)
                    ·
                      rfl

theorem cell22_1252789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_1252789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1252789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1252789 prefixEnd_1252789 := by exact prefixLift 1252789
  have htrace : WordTrace (prefixWord ++ tailWord_1252789) baseStart_1252789 baseEnd_1252789 := by
    simpa [prefixWord, tailWord_1252789, baseEnd_1252789] using wordTrace_append hprefix tailTrace_1252789
  have hstable : (prefixWord ++ tailWord_1252789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252789).length < 2 ^ (prefixWord ++ tailWord_1252789).sum := by decide
  have hdescent : baseEnd_1252789 < baseStart_1252789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252860 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 4, 4]
def baseStart_1252860 : Nat := 118140960795 + 1252860 * 2 ^ 59
def prefixEnd_1252860 : Nat := 4983230072969 + 3 ^ 40 * 1252860 * 2
def baseEnd_1252860 : Nat := 428879581861382275458805

theorem tailTrace_1252860 : CollatzResearch.WordTrace tailWord_1252860 prefixEnd_1252860 428879581861382275458805 := by
  unfold tailWord_1252860
  simp only [CollatzResearch.WordTrace]
  refine ⟨22847779120554833148986017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30463705494073110865314689 22847779120554833148986017)
  ·
    refine ⟨17135834340416124861739513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22847779120554833148986017 17135834340416124861739513)
    ·
      refine ⟨12851875755312093646304635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17135834340416124861739513 12851875755312093646304635)
      ·
        refine ⟨19277813632968140469456953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12851875755312093646304635 19277813632968140469456953)
        ·
          refine ⟨14458360224726105352092715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19277813632968140469456953 14458360224726105352092715)
          ·
            refine ⟨21687540337089158028139073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14458360224726105352092715 21687540337089158028139073)
            ·
              refine ⟨16265655252816868521104305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21687540337089158028139073 16265655252816868521104305)
              ·
                refine ⟨12199241439612651390828229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16265655252816868521104305 12199241439612651390828229)
                ·
                  refine ⟨2287357769927372135780293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12199241439612651390828229 2287357769927372135780293)
                  ·
                    refine ⟨428879581861382275458805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2287357769927372135780293 428879581861382275458805)
                    ·
                      rfl

theorem cell22_1252860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_1252860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1252860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1252860 prefixEnd_1252860 := by exact prefixLift 1252860
  have htrace : WordTrace (prefixWord ++ tailWord_1252860) baseStart_1252860 baseEnd_1252860 := by
    simpa [prefixWord, tailWord_1252860, baseEnd_1252860] using wordTrace_append hprefix tailTrace_1252860
  have hstable : (prefixWord ++ tailWord_1252860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252860).length < 2 ^ (prefixWord ++ tailWord_1252860).sum := by decide
  have hdescent : baseEnd_1252860 < baseStart_1252860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252896 : List Nat := [2, 1, 1, 6, 1, 3, 1, 2, 2, 3]
def baseStart_1252896 : Nat := 118140960795 + 1252896 * 2 ^ 59
def prefixEnd_1252896 : Nat := 4983230072969 + 3 ^ 40 * 1252896 * 2
def baseEnd_1252896 : Nat := 428891905397090181558695

theorem tailTrace_1252896 : CollatzResearch.WordTrace tailWord_1252896 prefixEnd_1252896 428891905397090181558695 := by
  unfold tailWord_1252896
  simp only [CollatzResearch.WordTrace]
  refine ⟨22848435634489622223141271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30464580845986162964188361 22848435634489622223141271)
  ·
    refine ⟨34272653451734433334711907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22848435634489622223141271 34272653451734433334711907)
    ·
      refine ⟨51408980177601650002067861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34272653451734433334711907 51408980177601650002067861)
      ·
        refine ⟨2409795945825077343846931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 51408980177601650002067861 2409795945825077343846931)
        ·
          refine ⟨3614693918737616015770397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2409795945825077343846931 3614693918737616015770397)
          ·
            refine ⟨1355510219526606005913899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3614693918737616015770397 1355510219526606005913899)
            ·
              refine ⟨2033265329289909008870849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1355510219526606005913899 2033265329289909008870849)
              ·
                refine ⟨1524948996967431756653137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2033265329289909008870849 1524948996967431756653137)
                ·
                  refine ⟨1143711747725573817489853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1524948996967431756653137 1143711747725573817489853)
                  ·
                    refine ⟨428891905397090181558695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1143711747725573817489853 428891905397090181558695)
                    ·
                      rfl

theorem cell22_1252896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 2, 3].length) (baseStart_1252896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1252896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1252896 prefixEnd_1252896 := by exact prefixLift 1252896
  have htrace : WordTrace (prefixWord ++ tailWord_1252896) baseStart_1252896 baseEnd_1252896 := by
    simpa [prefixWord, tailWord_1252896, baseEnd_1252896] using wordTrace_append hprefix tailTrace_1252896
  have hstable : (prefixWord ++ tailWord_1252896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252896).length < 2 ^ (prefixWord ++ tailWord_1252896).sum := by decide
  have hdescent : baseEnd_1252896 < baseStart_1252896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252997 : List Nat := [1, 3, 1, 1, 4, 1, 3, 2, 1, 5]
def baseStart_1252997 : Nat := 118140960795 + 1252997 * 2 ^ 59
def prefixEnd_1252997 : Nat := 4983230072969 + 3 ^ 40 * 1252997 * 2
def baseEnd_1252997 : Nat := 428926479761159584783385

theorem tailTrace_1252997 : CollatzResearch.WordTrace tailWord_1252997 prefixEnd_1252997 428926479761159584783385 := by
  unfold tailWord_1252997
  simp only [CollatzResearch.WordTrace]
  refine ⟨45700555041613338695709245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30467036694408892463806163 45700555041613338695709245)
  ·
    refine ⟨17137708140605002010890967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45700555041613338695709245 17137708140605002010890967)
    ·
      refine ⟨25706562210907503016336451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17137708140605002010890967 25706562210907503016336451)
      ·
        refine ⟨38559843316361254524504677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25706562210907503016336451 38559843316361254524504677)
        ·
          refine ⟨7229970621817735223344627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38559843316361254524504677 7229970621817735223344627)
          ·
            refine ⟨10844955932726602835016941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7229970621817735223344627 10844955932726602835016941)
            ·
              refine ⟨4066858474772476063131353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10844955932726602835016941 4066858474772476063131353)
              ·
                refine ⟨3050143856079357047348515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4066858474772476063131353 3050143856079357047348515)
                ·
                  refine ⟨4575215784119035571022773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3050143856079357047348515 4575215784119035571022773)
                  ·
                    refine ⟨428926479761159584783385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4575215784119035571022773 428926479761159584783385)
                    ·
                      rfl

theorem cell22_1252997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_1252997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1252997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1252997 prefixEnd_1252997 := by exact prefixLift 1252997
  have htrace : WordTrace (prefixWord ++ tailWord_1252997) baseStart_1252997 baseEnd_1252997 := by
    simpa [prefixWord, tailWord_1252997, baseEnd_1252997] using wordTrace_append hprefix tailTrace_1252997
  have hstable : (prefixWord ++ tailWord_1252997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252997).length < 2 ^ (prefixWord ++ tailWord_1252997).sum := by decide
  have hdescent : baseEnd_1252997 < baseStart_1252997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253016 : List Nat := [2, 1, 2, 4, 1, 2, 4, 2, 4]
def baseStart_1253016 : Nat := 118140960795 + 1253016 * 2 ^ 59
def prefixEnd_1253016 : Nat := 4983230072969 + 3 ^ 40 * 1253016 * 2
def baseEnd_1253016 : Nat := 142977661283149956186109

theorem tailTrace_1253016 : CollatzResearch.WordTrace tailWord_1253016 prefixEnd_1253016 142977661283149956186109 := by
  unfold tailWord_1253016
  simp only [CollatzResearch.WordTrace]
  refine ⟨22850624014272252470325451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30467498685696336627100601 22850624014272252470325451)
  ·
    refine ⟨34275936021408378705488177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22850624014272252470325451 34275936021408378705488177)
    ·
      refine ⟨25706952016056284029116133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34275936021408378705488177 25706952016056284029116133)
      ·
        refine ⟨4820053503010553255459275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25706952016056284029116133 4820053503010553255459275)
        ·
          refine ⟨7230080254515829883188913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4820053503010553255459275 7230080254515829883188913)
          ·
            refine ⟨5422560190886872412391685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7230080254515829883188913 5422560190886872412391685)
            ·
              refine ⟨1016730035791288577323441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5422560190886872412391685 1016730035791288577323441)
              ·
                refine ⟨762547526843466432992581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1016730035791288577323441 762547526843466432992581)
                ·
                  refine ⟨142977661283149956186109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 762547526843466432992581 142977661283149956186109)
                  ·
                    rfl

theorem cell22_1253016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 2, 4].length) (baseStart_1253016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253016 prefixEnd_1253016 := by exact prefixLift 1253016
  have htrace : WordTrace (prefixWord ++ tailWord_1253016) baseStart_1253016 baseEnd_1253016 := by
    simpa [prefixWord, tailWord_1253016, baseEnd_1253016] using wordTrace_append hprefix tailTrace_1253016
  have hstable : (prefixWord ++ tailWord_1253016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253016).length < 2 ^ (prefixWord ++ tailWord_1253016).sum := by decide
  have hdescent : baseEnd_1253016 < baseStart_1253016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253046 : List Nat := [5, 1, 3, 1, 1, 2, 1, 1, 1, 6]
def baseStart_1253046 : Nat := 118140960795 + 1253046 * 2 ^ 59
def prefixEnd_1253046 : Nat := 4983230072969 + 3 ^ 40 * 1253046 * 2
def baseEnd_1253046 : Nat := 428943253462539790308235

theorem tailTrace_1253046 : CollatzResearch.WordTrace tailWord_1253046 prefixEnd_1253046 428943253462539790308235 := by
  unfold tailWord_1253046
  simp only [CollatzResearch.WordTrace]
  refine ⟨2856396388652238754015187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30468228145623880042828661 2856396388652238754015187)
  ·
    refine ⟨4284594582978358131022781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2856396388652238754015187 4284594582978358131022781)
    ·
      refine ⟨1606722968616884299133543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4284594582978358131022781 1606722968616884299133543)
      ·
        refine ⟨2410084452925326448700315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1606722968616884299133543 2410084452925326448700315)
        ·
          refine ⟨3615126679387989673050473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2410084452925326448700315 3615126679387989673050473)
          ·
            refine ⟨2711345009540992254787855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3615126679387989673050473 2711345009540992254787855)
            ·
              refine ⟨4067017514311488382181783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2711345009540992254787855 4067017514311488382181783)
              ·
                refine ⟨6100526271467232573272675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4067017514311488382181783 6100526271467232573272675)
                ·
                  refine ⟨9150789407200848859909013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6100526271467232573272675 9150789407200848859909013)
                  ·
                    refine ⟨428943253462539790308235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9150789407200848859909013 428943253462539790308235)
                    ·
                      rfl

theorem cell22_1253046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_1253046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253046 prefixEnd_1253046 := by exact prefixLift 1253046
  have htrace : WordTrace (prefixWord ++ tailWord_1253046) baseStart_1253046 baseEnd_1253046 := by
    simpa [prefixWord, tailWord_1253046, baseEnd_1253046] using wordTrace_append hprefix tailTrace_1253046
  have hstable : (prefixWord ++ tailWord_1253046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253046).length < 2 ^ (prefixWord ++ tailWord_1253046).sum := by decide
  have hdescent : baseEnd_1253046 < baseStart_1253046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253072 : List Nat := [2, 1, 1, 1, 1, 2, 1, 8, 5]
def baseStart_1253072 : Nat := 118140960795 + 1253072 * 2 ^ 59
def prefixEnd_1253072 : Nat := 4983230072969 + 3 ^ 40 * 1253072 * 2
def baseEnd_1253072 : Nat := 142984051264628129719385

theorem tailTrace_1253072 : CollatzResearch.WordTrace tailWord_1253072 prefixEnd_1253072 142984051264628129719385 := by
  unfold tailWord_1253072
  simp only [CollatzResearch.WordTrace]
  refine ⟨22851645258170813252344735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30468860344227751003126313 22851645258170813252344735)
  ·
    refine ⟨34277467887256219878517103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22851645258170813252344735 34277467887256219878517103)
    ·
      refine ⟨51416201830884329817775655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34277467887256219878517103 51416201830884329817775655)
      ·
        refine ⟨77124302746326494726663483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51416201830884329817775655 77124302746326494726663483)
        ·
          refine ⟨115686454119489742089995225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77124302746326494726663483 115686454119489742089995225)
          ·
            refine ⟨86764840589617306567496419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115686454119489742089995225 86764840589617306567496419)
            ·
              refine ⟨130147260884425959851244629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86764840589617306567496419 130147260884425959851244629)
              ·
                refine ⟨1525163213489366717006773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 130147260884425959851244629 1525163213489366717006773)
                ·
                  refine ⟨142984051264628129719385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1525163213489366717006773 142984051264628129719385)
                  ·
                    rfl

theorem cell22_1253072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 5].length) (baseStart_1253072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253072 prefixEnd_1253072 := by exact prefixLift 1253072
  have htrace : WordTrace (prefixWord ++ tailWord_1253072) baseStart_1253072 baseEnd_1253072 := by
    simpa [prefixWord, tailWord_1253072, baseEnd_1253072] using wordTrace_append hprefix tailTrace_1253072
  have hstable : (prefixWord ++ tailWord_1253072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253072).length < 2 ^ (prefixWord ++ tailWord_1253072).sum := by decide
  have hdescent : baseEnd_1253072 < baseStart_1253072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253076 : List Nat := [2, 4, 1, 3, 1, 1, 1, 3, 3, 3]
def baseStart_1253076 : Nat := 118140960795 + 1253076 * 2 ^ 59
def prefixEnd_1253076 : Nat := 4983230072969 + 3 ^ 40 * 1253076 * 2
def baseEnd_1253076 : Nat := 428953523075629712058143

theorem tailTrace_1253076 : CollatzResearch.WordTrace tailWord_1253076 prefixEnd_1253076 428953523075629712058143 := by
  unfold tailWord_1253076
  simp only [CollatzResearch.WordTrace]
  refine ⟨22851718204163567593917541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30468957605551423458556721 22851718204163567593917541)
  ·
    refine ⟨4284697163280668923859539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22851718204163567593917541 4284697163280668923859539)
    ·
      refine ⟨6427045744921003385789309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4284697163280668923859539 6427045744921003385789309)
      ·
        refine ⟨2410142154345376269670991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6427045744921003385789309 2410142154345376269670991)
        ·
          refine ⟨3615213231518064404506487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2410142154345376269670991 3615213231518064404506487)
          ·
            refine ⟨5422819847277096606759731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3615213231518064404506487 5422819847277096606759731)
            ·
              refine ⟨8134229770915644910139597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5422819847277096606759731 8134229770915644910139597)
              ·
                refine ⟨3050336164093366841302349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8134229770915644910139597 3050336164093366841302349)
                ·
                  refine ⟨1143876061535012565488381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3050336164093366841302349 1143876061535012565488381)
                  ·
                    refine ⟨428953523075629712058143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1143876061535012565488381 428953523075629712058143)
                    ·
                      rfl

theorem cell22_1253076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_1253076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253076 prefixEnd_1253076 := by exact prefixLift 1253076
  have htrace : WordTrace (prefixWord ++ tailWord_1253076) baseStart_1253076 baseEnd_1253076 := by
    simpa [prefixWord, tailWord_1253076, baseEnd_1253076] using wordTrace_append hprefix tailTrace_1253076
  have hstable : (prefixWord ++ tailWord_1253076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253076).length < 2 ^ (prefixWord ++ tailWord_1253076).sum := by decide
  have hdescent : baseEnd_1253076 < baseStart_1253076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253087 : List Nat := [1, 1, 2, 3, 2, 2, 1, 3, 2, 5]
def baseStart_1253087 : Nat := 118140960795 + 1253087 * 2 ^ 59
def prefixEnd_1253087 : Nat := 4983230072969 + 3 ^ 40 * 1253087 * 2
def baseEnd_1253087 : Nat := 428957288600429350033109

theorem tailTrace_1253087 : CollatzResearch.WordTrace tailWord_1253087 prefixEnd_1253087 428957288600429350033109 := by
  unfold tailWord_1253087
  simp only [CollatzResearch.WordTrace]
  refine ⟨45703837611287284066485515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30469225074191522710990343 45703837611287284066485515)
  ·
    refine ⟨68555756416930926099728273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45703837611287284066485515 68555756416930926099728273)
    ·
      refine ⟨51416817312698194574796205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68555756416930926099728273 51416817312698194574796205)
      ·
        refine ⟨19281306492261822965548577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51416817312698194574796205 19281306492261822965548577)
        ·
          refine ⟨14460979869196367224161433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19281306492261822965548577 14460979869196367224161433)
          ·
            refine ⟨10845734901897275418121075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14460979869196367224161433 10845734901897275418121075)
            ·
              refine ⟨16268602352845913127181613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10845734901897275418121075 16268602352845913127181613)
              ·
                refine ⟨6100725882317217422693105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16268602352845913127181613 6100725882317217422693105)
                ·
                  refine ⟨4575544411737913067019829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6100725882317217422693105 4575544411737913067019829)
                  ·
                    refine ⟨428957288600429350033109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4575544411737913067019829 428957288600429350033109)
                    ·
                      rfl

theorem cell22_1253087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 5].length) (baseStart_1253087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253087 prefixEnd_1253087 := by exact prefixLift 1253087
  have htrace : WordTrace (prefixWord ++ tailWord_1253087) baseStart_1253087 baseEnd_1253087 := by
    simpa [prefixWord, tailWord_1253087, baseEnd_1253087] using wordTrace_append hprefix tailTrace_1253087
  have hstable : (prefixWord ++ tailWord_1253087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253087).length < 2 ^ (prefixWord ++ tailWord_1253087).sum := by decide
  have hdescent : baseEnd_1253087 < baseStart_1253087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253110 : List Nat := [5, 1, 1, 1, 1, 5, 1, 3, 1, 3]
def baseStart_1253110 : Nat := 118140960795 + 1253110 * 2 ^ 59
def prefixEnd_1253110 : Nat := 4983230072969 + 3 ^ 40 * 1253110 * 2
def baseEnd_1253110 : Nat := 428965161970464956708039

theorem tailTrace_1253110 : CollatzResearch.WordTrace tailWord_1253110 prefixEnd_1253110 428965161970464956708039 := by
  unfold tailWord_1253110
  simp only [CollatzResearch.WordTrace]
  refine ⟨2856542280637747437160799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30469784326802639329715189 2856542280637747437160799)
  ·
    refine ⟨4284813420956621155741199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2856542280637747437160799 4284813420956621155741199)
    ·
      refine ⟨6427220131434931733611799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4284813420956621155741199 6427220131434931733611799)
      ·
        refine ⟨9640830197152397600417699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6427220131434931733611799 9640830197152397600417699)
        ·
          refine ⟨14461245295728596400626549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9640830197152397600417699 14461245295728596400626549)
          ·
            refine ⟨1355741746474555912558739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14461245295728596400626549 1355741746474555912558739)
            ·
              refine ⟨2033612619711833868838109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1355741746474555912558739 2033612619711833868838109)
              ·
                refine ⟨762604732391937700814291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2033612619711833868838109 762604732391937700814291)
                ·
                  refine ⟨1143907098587906551221437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 762604732391937700814291 1143907098587906551221437)
                  ·
                    refine ⟨428965161970464956708039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1143907098587906551221437 428965161970464956708039)
                    ·
                      rfl

theorem cell22_1253110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_1253110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253110 prefixEnd_1253110 := by exact prefixLift 1253110
  have htrace : WordTrace (prefixWord ++ tailWord_1253110) baseStart_1253110 baseEnd_1253110 := by
    simpa [prefixWord, tailWord_1253110, baseEnd_1253110] using wordTrace_append hprefix tailTrace_1253110
  have hstable : (prefixWord ++ tailWord_1253110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253110).length < 2 ^ (prefixWord ++ tailWord_1253110).sum := by decide
  have hdescent : baseEnd_1253110 < baseStart_1253110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253119 : List Nat := [1, 1, 2, 2, 1, 3, 4, 3, 1, 4]
def baseStart_1253119 : Nat := 118140960795 + 1253119 * 2 ^ 59
def prefixEnd_1253119 : Nat := 4983230072969 + 3 ^ 40 * 1253119 * 2
def baseEnd_1253119 : Nat := 428968242854391933233011

theorem tailTrace_1253119 : CollatzResearch.WordTrace tailWord_1253119 prefixEnd_1253119 428968242854391933233011 := by
  unfold tailWord_1253119
  simp only [CollatzResearch.WordTrace]
  refine ⟨45705004747171353531650411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30470003164780902354433607 45705004747171353531650411)
  ·
    refine ⟨68557507120757030297475617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45705004747171353531650411 68557507120757030297475617)
    ·
      refine ⟨51418130340567772723106713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68557507120757030297475617 51418130340567772723106713)
      ·
        refine ⟨38563597755425829542330035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51418130340567772723106713 38563597755425829542330035)
        ·
          refine ⟨57845396633138744313495053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38563597755425829542330035 57845396633138744313495053)
          ·
            refine ⟨21692023737427029117560645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57845396633138744313495053 21692023737427029117560645)
            ·
              refine ⟨4067254450767567959542621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21692023737427029117560645 4067254450767567959542621)
              ·
                refine ⟨1525220419037837984828483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4067254450767567959542621 1525220419037837984828483)
                ·
                  refine ⟨2287830628556756977242725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1525220419037837984828483 2287830628556756977242725)
                  ·
                    refine ⟨428968242854391933233011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2287830628556756977242725 428968242854391933233011)
                    ·
                      rfl

theorem cell22_1253119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 4].length) (baseStart_1253119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253119 prefixEnd_1253119 := by exact prefixLift 1253119
  have htrace : WordTrace (prefixWord ++ tailWord_1253119) baseStart_1253119 baseEnd_1253119 := by
    simpa [prefixWord, tailWord_1253119, baseEnd_1253119] using wordTrace_append hprefix tailTrace_1253119
  have hstable : (prefixWord ++ tailWord_1253119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253119).length < 2 ^ (prefixWord ++ tailWord_1253119).sum := by decide
  have hdescent : baseEnd_1253119 < baseStart_1253119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253134 : List Nat := [4, 1, 1, 2, 1, 1, 5, 1, 6]
def baseStart_1253134 : Nat := 118140960795 + 1253134 * 2 ^ 59
def prefixEnd_1253134 : Nat := 4983230072969 + 3 ^ 40 * 1253134 * 2
def baseEnd_1253134 : Nat := 142991125886978964702655

theorem tailTrace_1253134 : CollatzResearch.WordTrace tailWord_1253134 prefixEnd_1253134 142991125886978964702655 := by
  unfold tailWord_1253134
  simp only [CollatzResearch.WordTrace]
  refine ⟨5713193980264626386680807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30470367894744674062297637 5713193980264626386680807)
  ·
    refine ⟨8569790970396939580021211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5713193980264626386680807 8569790970396939580021211)
    ·
      refine ⟨12854686455595409370031817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8569790970396939580021211 12854686455595409370031817)
      ·
        refine ⟨9641014841696557027523863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12854686455595409370031817 9641014841696557027523863)
        ·
          refine ⟨14461522262544835541285795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9641014841696557027523863 14461522262544835541285795)
          ·
            refine ⟨21692283393817253311928693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14461522262544835541285795 21692283393817253311928693)
            ·
              refine ⟨2033651568170367497993315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21692283393817253311928693 2033651568170367497993315)
              ·
                refine ⟨3050477352255551246989973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2033651568170367497993315 3050477352255551246989973)
                ·
                  refine ⟨142991125886978964702655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3050477352255551246989973 142991125886978964702655)
                  ·
                    rfl

theorem cell22_1253134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_1253134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253134 prefixEnd_1253134 := by exact prefixLift 1253134
  have htrace : WordTrace (prefixWord ++ tailWord_1253134) baseStart_1253134 baseEnd_1253134 := by
    simpa [prefixWord, tailWord_1253134, baseEnd_1253134] using wordTrace_append hprefix tailTrace_1253134
  have hstable : (prefixWord ++ tailWord_1253134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253134).length < 2 ^ (prefixWord ++ tailWord_1253134).sum := by decide
  have hdescent : baseEnd_1253134 < baseStart_1253134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253140 : List Nat := [2, 4, 4, 1, 1, 1, 1, 3, 5]
def baseStart_1253140 : Nat := 118140960795 + 1253140 * 2 ^ 59
def prefixEnd_1253140 : Nat := 4983230072969 + 3 ^ 40 * 1253140 * 2
def baseEnd_1253140 : Nat := 142991810527851626152649

theorem tailTrace_1253140 : CollatzResearch.WordTrace tailWord_1253140 prefixEnd_1253140 142991810527851626152649 := by
  unfold tailWord_1253140
  simp only [CollatzResearch.WordTrace]
  refine ⟨22852885340047637059082437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30470513786730182745443249 22852885340047637059082437)
  ·
    refine ⟨4284916001258931948577957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22852885340047637059082437 4284916001258931948577957)
    ·
      refine ⟨803421750236049740358367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4284916001258931948577957 803421750236049740358367)
      ·
        refine ⟨1205132625354074610537551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 803421750236049740358367 1205132625354074610537551)
        ·
          refine ⟨1807698938031111915806327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1205132625354074610537551 1807698938031111915806327)
          ·
            refine ⟨2711548407046667873709491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1807698938031111915806327 2711548407046667873709491)
            ·
              refine ⟨4067322610570001810564237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2711548407046667873709491 4067322610570001810564237)
              ·
                refine ⟨1525245978963750678961589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4067322610570001810564237 1525245978963750678961589)
                ·
                  refine ⟨142991810527851626152649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1525245978963750678961589 142991810527851626152649)
                  ·
                    rfl

theorem cell22_1253140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_1253140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253140 prefixEnd_1253140 := by exact prefixLift 1253140
  have htrace : WordTrace (prefixWord ++ tailWord_1253140) baseStart_1253140 baseEnd_1253140 := by
    simpa [prefixWord, tailWord_1253140, baseEnd_1253140] using wordTrace_append hprefix tailTrace_1253140
  have hstable : (prefixWord ++ tailWord_1253140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253140).length < 2 ^ (prefixWord ++ tailWord_1253140).sum := by decide
  have hdescent : baseEnd_1253140 < baseStart_1253140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253164 : List Nat := [2, 2, 1, 1, 1, 5, 1, 3, 2, 4]
def baseStart_1253164 : Nat := 118140960795 + 1253164 * 2 ^ 59
def prefixEnd_1253164 : Nat := 4983230072969 + 3 ^ 40 * 1253164 * 2
def baseEnd_1253164 : Nat := 428983647274026815857873

theorem tailTrace_1253164 : CollatzResearch.WordTrace tailWord_1253164 prefixEnd_1253164 428983647274026815857873 := by
  unfold tailWord_1253164
  simp only [CollatzResearch.WordTrace]
  refine ⟨22853323016004163108519273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30471097354672217478025697 22853323016004163108519273)
  ·
    refine ⟨17139992262003122331389455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22853323016004163108519273 17139992262003122331389455)
    ·
      refine ⟨25709988393004683497084183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17139992262003122331389455 25709988393004683497084183)
      ·
        refine ⟨38564982589507025245626275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25709988393004683497084183 38564982589507025245626275)
        ·
          refine ⟨57847473884260537868439413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38564982589507025245626275 57847473884260537868439413)
          ·
            refine ⟨5423200676649425425166195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57847473884260537868439413 5423200676649425425166195)
            ·
              refine ⟨8134801014974138137749293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5423200676649425425166195 8134801014974138137749293)
              ·
                refine ⟨3050550380615301801655985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8134801014974138137749293 3050550380615301801655985)
                ·
                  refine ⟨2287912785461476351241989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3050550380615301801655985 2287912785461476351241989)
                  ·
                    refine ⟨428983647274026815857873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2287912785461476351241989 428983647274026815857873)
                    ·
                      rfl

theorem cell22_1253164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_1253164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253164 prefixEnd_1253164 := by exact prefixLift 1253164
  have htrace : WordTrace (prefixWord ++ tailWord_1253164) baseStart_1253164 baseEnd_1253164 := by
    simpa [prefixWord, tailWord_1253164, baseEnd_1253164] using wordTrace_append hprefix tailTrace_1253164
  have hstable : (prefixWord ++ tailWord_1253164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253164).length < 2 ^ (prefixWord ++ tailWord_1253164).sum := by decide
  have hdescent : baseEnd_1253164 < baseStart_1253164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253181 : List Nat := [1, 4, 1, 4, 1, 1, 2, 2, 2, 4]
def baseStart_1253181 : Nat := 118140960795 + 1253181 * 2 ^ 59
def prefixEnd_1253181 : Nat := 4983230072969 + 3 ^ 40 * 1253181 * 2
def baseEnd_1253181 : Nat := 428989466721444438182821

theorem tailTrace_1253181 : CollatzResearch.WordTrace tailWord_1253181 prefixEnd_1253181 428989466721444438182821 := by
  unfold tailWord_1253181
  simp only [CollatzResearch.WordTrace]
  refine ⟨45707266072946738120407397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30471510715297825413604931 45707266072946738120407397)
  ·
    refine ⟨8570112388677513397576387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45707266072946738120407397 8570112388677513397576387)
    ·
      refine ⟨12855168583016270096364581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8570112388677513397576387 12855168583016270096364581)
      ·
        refine ⟨2410344109315550643068359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12855168583016270096364581 2410344109315550643068359)
        ·
          refine ⟨3615516163973325964602539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2410344109315550643068359 3615516163973325964602539)
          ·
            refine ⟨5423274245959988946903809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3615516163973325964602539 5423274245959988946903809)
            ·
              refine ⟨4067455684469991710177857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5423274245959988946903809 4067455684469991710177857)
              ·
                refine ⟨3050591763352493782633393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4067455684469991710177857 3050591763352493782633393)
                ·
                  refine ⟨2287943822514370336975045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3050591763352493782633393 2287943822514370336975045)
                  ·
                    refine ⟨428989466721444438182821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2287943822514370336975045 428989466721444438182821)
                    ·
                      rfl

theorem cell22_1253181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_1253181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253181 prefixEnd_1253181 := by exact prefixLift 1253181
  have htrace : WordTrace (prefixWord ++ tailWord_1253181) baseStart_1253181 baseEnd_1253181 := by
    simpa [prefixWord, tailWord_1253181, baseEnd_1253181] using wordTrace_append hprefix tailTrace_1253181
  have hstable : (prefixWord ++ tailWord_1253181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253181).length < 2 ^ (prefixWord ++ tailWord_1253181).sum := by decide
  have hdescent : baseEnd_1253181 < baseStart_1253181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253183 : List Nat := [1, 1, 2, 2, 6, 1, 2, 2, 2, 3]
def baseStart_1253183 : Nat := 118140960795 + 1253183 * 2 ^ 59
def prefixEnd_1253183 : Nat := 4983230072969 + 3 ^ 40 * 1253183 * 2
def baseEnd_1253183 : Nat := 428990151362317099632815

theorem tailTrace_1253183 : CollatzResearch.WordTrace tailWord_1253183 prefixEnd_1253183 428990151362317099632815 := by
  unfold tailWord_1253183
  simp only [CollatzResearch.WordTrace]
  refine ⟨45707339018939492461980203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30471559345959661641320135 45707339018939492461980203)
  ·
    refine ⟨68561008528409238692970305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45707339018939492461980203 68561008528409238692970305)
    ·
      refine ⟨51420756396306929019727729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68561008528409238692970305 51420756396306929019727729)
      ·
        refine ⟨38565567297230196764795797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51420756396306929019727729 38565567297230196764795797)
        ·
          refine ⟨1807760967057665473349803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 38565567297230196764795797 1807760967057665473349803)
          ·
            refine ⟨2711641450586498210024705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1807760967057665473349803 2711641450586498210024705)
            ·
              refine ⟨2033731087939873657518529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2711641450586498210024705 2033731087939873657518529)
              ·
                refine ⟨1525298315954905243138897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2033731087939873657518529 1525298315954905243138897)
                ·
                  refine ⟨1143973736966178932354173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1525298315954905243138897 1143973736966178932354173)
                  ·
                    refine ⟨428990151362317099632815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1143973736966178932354173 428990151362317099632815)
                    ·
                      rfl

theorem cell22_1253183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 2, 3].length) (baseStart_1253183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253183 prefixEnd_1253183 := by exact prefixLift 1253183
  have htrace : WordTrace (prefixWord ++ tailWord_1253183) baseStart_1253183 baseEnd_1253183 := by
    simpa [prefixWord, tailWord_1253183, baseEnd_1253183] using wordTrace_append hprefix tailTrace_1253183
  have hstable : (prefixWord ++ tailWord_1253183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253183).length < 2 ^ (prefixWord ++ tailWord_1253183).sum := by decide
  have hdescent : baseEnd_1253183 < baseStart_1253183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253196 : List Nat := [2, 2, 1, 3, 4, 2, 1, 7]
def baseStart_1253196 : Nat := 118140960795 + 1253196 * 2 ^ 59
def prefixEnd_1253196 : Nat := 4983230072969 + 3 ^ 40 * 1253196 * 2
def baseEnd_1253196 : Nat := 47666066836443266561975

theorem tailTrace_1253196 : CollatzResearch.WordTrace tailWord_1253196 prefixEnd_1253196 47666066836443266561975 := by
  unfold tailWord_1253196
  simp only [CollatzResearch.WordTrace]
  refine ⟨22853906583946197841101721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30471875445261597121468961 22853906583946197841101721)
  ·
    refine ⟨17140429937959648380826291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22853906583946197841101721 17140429937959648380826291)
    ·
      refine ⟨25710644906939472571239437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17140429937959648380826291 25710644906939472571239437)
      ·
        refine ⟨9641491840102302214214789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25710644906939472571239437 9641491840102302214214789)
        ·
          refine ⟨1807779720019181665165273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9641491840102302214214789 1807779720019181665165273)
          ·
            refine ⟨1355834790014386248873955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1807779720019181665165273 1355834790014386248873955)
            ·
              refine ⟨2033752185021579373310933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1355834790014386248873955 2033752185021579373310933)
              ·
                refine ⟨47666066836443266561975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2033752185021579373310933 47666066836443266561975)
                ·
                  rfl

theorem cell22_1253196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 7].length) (baseStart_1253196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253196 prefixEnd_1253196 := by exact prefixLift 1253196
  have htrace : WordTrace (prefixWord ++ tailWord_1253196) baseStart_1253196 baseEnd_1253196 := by
    simpa [prefixWord, tailWord_1253196, baseEnd_1253196] using wordTrace_append hprefix tailTrace_1253196
  have hstable : (prefixWord ++ tailWord_1253196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253196).length < 2 ^ (prefixWord ++ tailWord_1253196).sum := by decide
  have hdescent : baseEnd_1253196 < baseStart_1253196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253224 : List Nat := [2, 1, 4, 2, 1, 1, 2, 2, 7]
def baseStart_1253224 : Nat := 118140960795 + 1253224 * 2 ^ 59
def prefixEnd_1253224 : Nat := 4983230072969 + 3 ^ 40 * 1253224 * 2
def baseEnd_1253224 : Nat := 143001395500068886452563

theorem tailTrace_1253224 : CollatzResearch.WordTrace tailWord_1253224 prefixEnd_1253224 143001395500068886452563 := by
  unfold tailWord_1253224
  simp only [CollatzResearch.WordTrace]
  refine ⟨22854417205895478232111363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30472556274527304309481817 22854417205895478232111363)
  ·
    refine ⟨34281625808843217348167045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22854417205895478232111363 34281625808843217348167045)
    ·
      refine ⟨6427804839158103252781321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34281625808843217348167045 6427804839158103252781321)
      ·
        refine ⟨4820853629368577439585991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6427804839158103252781321 4820853629368577439585991)
        ·
          refine ⟨7231280444052866159378987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4820853629368577439585991 7231280444052866159378987)
          ·
            refine ⟨10846920666079299239068481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7231280444052866159378987 10846920666079299239068481)
            ·
              refine ⟨8135190499559474429301361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10846920666079299239068481 8135190499559474429301361)
              ·
                refine ⟨6101392874669605821976021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8135190499559474429301361 6101392874669605821976021)
                ·
                  refine ⟨143001395500068886452563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6101392874669605821976021 143001395500068886452563)
                  ·
                    rfl

theorem cell22_1253224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 7].length) (baseStart_1253224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253224 prefixEnd_1253224 := by exact prefixLift 1253224
  have htrace : WordTrace (prefixWord ++ tailWord_1253224) baseStart_1253224 baseEnd_1253224 := by
    simpa [prefixWord, tailWord_1253224, baseEnd_1253224] using wordTrace_append hprefix tailTrace_1253224
  have hstable : (prefixWord ++ tailWord_1253224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253224).length < 2 ^ (prefixWord ++ tailWord_1253224).sum := by decide
  have hdescent : baseEnd_1253224 < baseStart_1253224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253228 : List Nat := [2, 2, 1, 1, 4, 2, 1, 5, 1, 3]
def baseStart_1253228 : Nat := 118140960795 + 1253228 * 2 ^ 59
def prefixEnd_1253228 : Nat := 4983230072969 + 3 ^ 40 * 1253228 * 2
def baseEnd_1253228 : Nat := 429005555781951982257677

theorem tailTrace_1253228 : CollatzResearch.WordTrace tailWord_1253228 prefixEnd_1253228 429005555781951982257677 := by
  unfold tailWord_1253228
  simp only [CollatzResearch.WordTrace]
  refine ⟨22854490151888232573684169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30472653535850976764912225 22854490151888232573684169)
  ·
    refine ⟨17140867613916174430263127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22854490151888232573684169 17140867613916174430263127)
    ·
      refine ⟨25711301420874261645394691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17140867613916174430263127 25711301420874261645394691)
      ·
        refine ⟨38566952131311392468092037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25711301420874261645394691 38566952131311392468092037)
        ·
          refine ⟨7231303524620886087767257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38566952131311392468092037 7231303524620886087767257)
          ·
            refine ⟨5423477643465664565825443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7231303524620886087767257 5423477643465664565825443)
            ·
              refine ⟨8135216465198496848738165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5423477643465664565825443 8135216465198496848738165)
              ·
                refine ⟨762676543612359079569203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8135216465198496848738165 762676543612359079569203)
                ·
                  refine ⟨1144014815418538619353805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 762676543612359079569203 1144014815418538619353805)
                  ·
                    refine ⟨429005555781951982257677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1144014815418538619353805 429005555781951982257677)
                    ·
                      rfl

theorem cell22_1253228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 5, 1, 3].length) (baseStart_1253228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253228 prefixEnd_1253228 := by exact prefixLift 1253228
  have htrace : WordTrace (prefixWord ++ tailWord_1253228) baseStart_1253228 baseEnd_1253228 := by
    simpa [prefixWord, tailWord_1253228, baseEnd_1253228] using wordTrace_append hprefix tailTrace_1253228
  have hstable : (prefixWord ++ tailWord_1253228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253228).length < 2 ^ (prefixWord ++ tailWord_1253228).sum := by decide
  have hdescent : baseEnd_1253228 < baseStart_1253228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253269 : List Nat := [1, 3, 2, 1, 1, 3, 1, 4, 6]
def baseStart_1253269 : Nat := 118140960795 + 1253269 * 2 ^ 59
def prefixEnd_1253269 : Nat := 4983230072969 + 3 ^ 40 * 1253269 * 2
def baseEnd_1253269 : Nat := 143006530306613847327517

theorem tailTrace_1253269 : CollatzResearch.WordTrace tailWord_1253269 prefixEnd_1253269 143006530306613847327517 := by
  unfold tailWord_1253269
  simp only [CollatzResearch.WordTrace]
  refine ⟨45710475696627929149610861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30473650464418619433073907 45710475696627929149610861)
  ·
    refine ⟨17141428386235473431104073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45710475696627929149610861 17141428386235473431104073)
    ·
      refine ⟨12856071289676605073328055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17141428386235473431104073 12856071289676605073328055)
      ·
        refine ⟨19284106934514907609992083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12856071289676605073328055 19284106934514907609992083)
        ·
          refine ⟨28926160401772361414988125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19284106934514907609992083 28926160401772361414988125)
          ·
            refine ⟨10847310150664635530620547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28926160401772361414988125 10847310150664635530620547)
            ·
              refine ⟨16270965225996953295930821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10847310150664635530620547 16270965225996953295930821)
              ·
                refine ⟨3050805979874428742987029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16270965225996953295930821 3050805979874428742987029)
                ·
                  refine ⟨143006530306613847327517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3050805979874428742987029 143006530306613847327517)
                  ·
                    rfl

theorem cell22_1253269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 6].length) (baseStart_1253269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253269 prefixEnd_1253269 := by exact prefixLift 1253269
  have htrace : WordTrace (prefixWord ++ tailWord_1253269) baseStart_1253269 baseEnd_1253269 := by
    simpa [prefixWord, tailWord_1253269, baseEnd_1253269] using wordTrace_append hprefix tailTrace_1253269
  have hstable : (prefixWord ++ tailWord_1253269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253269).length < 2 ^ (prefixWord ++ tailWord_1253269).sum := by decide
  have hdescent : baseEnd_1253269 < baseStart_1253269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253271 : List Nat := [1, 1, 3, 3, 1, 3, 1, 4, 1, 4]
def baseStart_1253271 : Nat := 118140960795 + 1253271 * 2 ^ 59
def prefixEnd_1253271 : Nat := 4983230072969 + 3 ^ 40 * 1253271 * 2
def baseEnd_1253271 : Nat := 429020275560714203432545

theorem tailTrace_1253271 : CollatzResearch.WordTrace tailWord_1253271 prefixEnd_1253271 429020275560714203432545 := by
  unfold tailWord_1253271
  simp only [CollatzResearch.WordTrace]
  refine ⟨45710548642620683491183667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30473699095080455660789111 45710548642620683491183667)
  ·
    refine ⟨68565822963931025236775501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45710548642620683491183667 68565822963931025236775501)
    ·
      refine ⟨25712183611474134463790813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68565822963931025236775501 25712183611474134463790813)
      ·
        refine ⟨9642068854302800423921555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25712183611474134463790813 9642068854302800423921555)
        ·
          refine ⟨14463103281454200635882333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9642068854302800423921555 14463103281454200635882333)
          ·
            refine ⟨5423663730545325238455875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14463103281454200635882333 5423663730545325238455875)
            ·
              refine ⟨8135495595817987857683813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5423663730545325238455875 8135495595817987857683813)
              ·
                refine ⟨1525405424215872723315715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8135495595817987857683813 1525405424215872723315715)
                ·
                  refine ⟨2288108136323809084973573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1525405424215872723315715 2288108136323809084973573)
                  ·
                    refine ⟨429020275560714203432545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2288108136323809084973573 429020275560714203432545)
                    ·
                      rfl

theorem cell22_1253271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 4].length) (baseStart_1253271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253271 prefixEnd_1253271 := by exact prefixLift 1253271
  have htrace : WordTrace (prefixWord ++ tailWord_1253271) baseStart_1253271 baseEnd_1253271 := by
    simpa [prefixWord, tailWord_1253271, baseEnd_1253271] using wordTrace_append hprefix tailTrace_1253271
  have hstable : (prefixWord ++ tailWord_1253271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253271).length < 2 ^ (prefixWord ++ tailWord_1253271).sum := by decide
  have hdescent : baseEnd_1253271 < baseStart_1253271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253333 : List Nat := [1, 3, 2, 3, 2, 2, 2, 1, 2, 4]
def baseStart_1253333 : Nat := 118140960795 + 1253333 * 2 ^ 59
def prefixEnd_1253333 : Nat := 4983230072969 + 3 ^ 40 * 1253333 * 2
def baseEnd_1253333 : Nat := 429041499427766708382355

theorem tailTrace_1253333 : CollatzResearch.WordTrace tailWord_1253333 prefixEnd_1253333 429041499427766708382355 := by
  unfold tailWord_1253333
  simp only [CollatzResearch.WordTrace]
  refine ⟨45712809968396068079940653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30475206645597378719960435 45712809968396068079940653)
  ·
    refine ⟨17142303738148525529977745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45712809968396068079940653 17142303738148525529977745)
    ·
      refine ⟨12856727803611394147483309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17142303738148525529977745 12856727803611394147483309)
      ·
        refine ⟨4821272926354272805306241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12856727803611394147483309 4821272926354272805306241)
        ·
          refine ⟨3615954694765704603979681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4821272926354272805306241 3615954694765704603979681)
          ·
            refine ⟨2711966021074278452984761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3615954694765704603979681 2711966021074278452984761)
            ·
              refine ⟨2033974515805708839738571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2711966021074278452984761 2033974515805708839738571)
              ·
                refine ⟨3050961773708563259607857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2033974515805708839738571 3050961773708563259607857)
                ·
                  refine ⟨2288221330281422444705893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3050961773708563259607857 2288221330281422444705893)
                  ·
                    refine ⟨429041499427766708382355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2288221330281422444705893 429041499427766708382355)
                    ·
                      rfl

theorem cell22_1253333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_1253333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253333 prefixEnd_1253333 := by exact prefixLift 1253333
  have htrace : WordTrace (prefixWord ++ tailWord_1253333) baseStart_1253333 baseEnd_1253333 := by
    simpa [prefixWord, tailWord_1253333, baseEnd_1253333] using wordTrace_append hprefix tailTrace_1253333
  have hstable : (prefixWord ++ tailWord_1253333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253333).length < 2 ^ (prefixWord ++ tailWord_1253333).sum := by decide
  have hdescent : baseEnd_1253333 < baseStart_1253333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253344 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 4, 6]
def baseStart_1253344 : Nat := 118140960795 + 1253344 * 2 ^ 59
def prefixEnd_1253344 : Nat := 4983230072969 + 3 ^ 40 * 1253344 * 2
def baseEnd_1253344 : Nat := 429045264952566346357321

theorem tailTrace_1253344 : CollatzResearch.WordTrace tailWord_1253344 prefixEnd_1253344 429045264952566346357321 := by
  unfold tailWord_1253344
  simp only [CollatzResearch.WordTrace]
  refine ⟨22856605585678108479295543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30475474114237477972394057 22856605585678108479295543)
  ·
    refine ⟨34284908378517162718943315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22856605585678108479295543 34284908378517162718943315)
    ·
      refine ⟨51427362567775744078414973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34284908378517162718943315 51427362567775744078414973)
      ·
        refine ⟨19285260962915904029405615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51427362567775744078414973 19285260962915904029405615)
        ·
          refine ⟨28927891444373856044108423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19285260962915904029405615 28927891444373856044108423)
          ·
            refine ⟨43391837166560784066162635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28927891444373856044108423 43391837166560784066162635)
            ·
              refine ⟨65087755749841176099243953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43391837166560784066162635 65087755749841176099243953)
              ·
                refine ⟨48815816812380882074432965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65087755749841176099243953 48815816812380882074432965)
                ·
                  refine ⟨9152965652321415388956181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48815816812380882074432965 9152965652321415388956181)
                  ·
                    refine ⟨429045264952566346357321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9152965652321415388956181 429045264952566346357321)
                    ·
                      rfl

theorem cell22_1253344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 4, 6].length) (baseStart_1253344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253344 prefixEnd_1253344 := by exact prefixLift 1253344
  have htrace : WordTrace (prefixWord ++ tailWord_1253344) baseStart_1253344 baseEnd_1253344 := by
    simpa [prefixWord, tailWord_1253344, baseEnd_1253344] using wordTrace_append hprefix tailTrace_1253344
  have hstable : (prefixWord ++ tailWord_1253344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253344).length < 2 ^ (prefixWord ++ tailWord_1253344).sum := by decide
  have hdescent : baseEnd_1253344 < baseStart_1253344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253397 : List Nat := [1, 3, 2, 1, 5, 1, 2, 3, 1, 3]
def baseStart_1253397 : Nat := 118140960795 + 1253397 * 2 ^ 59
def prefixEnd_1253397 : Nat := 4983230072969 + 3 ^ 40 * 1253397 * 2
def baseEnd_1253397 : Nat := 429063407935691874782159

theorem tailTrace_1253397 : CollatzResearch.WordTrace tailWord_1253397 prefixEnd_1253397 429063407935691874782159 := by
  unfold tailWord_1253397
  simp only [CollatzResearch.WordTrace]
  refine ⟨45715144240164207010270445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30476762826776138006846963 45715144240164207010270445)
  ·
    refine ⟨17143179090061577628851417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45715144240164207010270445 17143179090061577628851417)
    ·
      refine ⟨12857384317546183221638563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17143179090061577628851417 12857384317546183221638563)
      ·
        refine ⟨19286076476319274832457845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12857384317546183221638563 19286076476319274832457845)
        ·
          refine ⟨1808069669654932015542923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19286076476319274832457845 1808069669654932015542923)
          ·
            refine ⟨2712104504482398023314385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1808069669654932015542923 2712104504482398023314385)
            ·
              refine ⟨2034078378361798517485789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2712104504482398023314385 2034078378361798517485789)
              ·
                refine ⟨762779391885674444057171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2034078378361798517485789 762779391885674444057171)
                ·
                  refine ⟨1144169087828511666085757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 762779391885674444057171 1144169087828511666085757)
                  ·
                    refine ⟨429063407935691874782159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1144169087828511666085757 429063407935691874782159)
                    ·
                      rfl

theorem cell22_1253397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 3, 1, 3].length) (baseStart_1253397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253397 prefixEnd_1253397 := by exact prefixLift 1253397
  have htrace : WordTrace (prefixWord ++ tailWord_1253397) baseStart_1253397 baseEnd_1253397 := by
    simpa [prefixWord, tailWord_1253397, baseEnd_1253397] using wordTrace_append hprefix tailTrace_1253397
  have hstable : (prefixWord ++ tailWord_1253397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253397).length < 2 ^ (prefixWord ++ tailWord_1253397).sum := by decide
  have hdescent : baseEnd_1253397 < baseStart_1253397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253453 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_1253453 : Nat := 118140960795 + 1253453 * 2 ^ 59
def prefixEnd_1253453 : Nat := 4983230072969 + 3 ^ 40 * 1253453 * 2
def baseEnd_1253453 : Nat := 429082577880126395381987

theorem tailTrace_1253453 : CollatzResearch.WordTrace tailWord_1253453 prefixEnd_1253453 429082577880126395381987 := by
  unfold tailWord_1253453
  simp only [CollatzResearch.WordTrace]
  refine ⟨45717186727961328574309013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30478124485307552382872675 45717186727961328574309013)
  ·
    refine ⟨2142993127873187276920735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 45717186727961328574309013 2142993127873187276920735)
    ·
      refine ⟨3214489691809780915381103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2142993127873187276920735 3214489691809780915381103)
      ·
        refine ⟨4821734537714671373071655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3214489691809780915381103 4821734537714671373071655)
        ·
          refine ⟨7232601806572007059607483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4821734537714671373071655 7232601806572007059607483)
          ·
            refine ⟨10848902709858010589411225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7232601806572007059607483 10848902709858010589411225)
            ·
              refine ⟨8136677032393507942058419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10848902709858010589411225 8136677032393507942058419)
              ·
                refine ⟨12205015548590261913087629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8136677032393507942058419 12205015548590261913087629)
                ·
                  refine ⟨4576880830721348217407861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12205015548590261913087629 4576880830721348217407861)
                  ·
                    refine ⟨429082577880126395381987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4576880830721348217407861 429082577880126395381987)
                    ·
                      rfl

theorem cell22_1253453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_1253453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253453 prefixEnd_1253453 := by exact prefixLift 1253453
  have htrace : WordTrace (prefixWord ++ tailWord_1253453) baseStart_1253453 baseEnd_1253453 := by
    simpa [prefixWord, tailWord_1253453, baseEnd_1253453] using wordTrace_append hprefix tailTrace_1253453
  have hstable : (prefixWord ++ tailWord_1253453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253453).length < 2 ^ (prefixWord ++ tailWord_1253453).sum := by decide
  have hdescent : baseEnd_1253453 < baseStart_1253453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253468 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 4, 4]
def baseStart_1253468 : Nat := 118140960795 + 1253468 * 2 ^ 59
def prefixEnd_1253468 : Nat := 4983230072969 + 3 ^ 40 * 1253468 * 2
def baseEnd_1253468 : Nat := 429087712686671356256941

theorem tailTrace_1253468 : CollatzResearch.WordTrace tailWord_1253468 prefixEnd_1253468 429087712686671356256941 := by
  unfold tailWord_1253468
  simp only [CollatzResearch.WordTrace]
  refine ⟨22858866911453493068052529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30478489215271324090736705 22858866911453493068052529)
  ·
    refine ⟨17144150183590119801039397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22858866911453493068052529 17144150183590119801039397)
    ·
      refine ⟨3214528159423147462694887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17144150183590119801039397 3214528159423147462694887)
      ·
        refine ⟨4821792239134721194042331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3214528159423147462694887 4821792239134721194042331)
        ·
          refine ⟨7232688358702081791063497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4821792239134721194042331 7232688358702081791063497)
          ·
            refine ⟨5424516269026561343297623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7232688358702081791063497 5424516269026561343297623)
            ·
              refine ⟨8136774403539842014946435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5424516269026561343297623 8136774403539842014946435)
              ·
                refine ⟨12205161605309763022419653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8136774403539842014946435 12205161605309763022419653)
                ·
                  refine ⟨2288467800995580566703685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12205161605309763022419653 2288467800995580566703685)
                  ·
                    refine ⟨429087712686671356256941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2288467800995580566703685 429087712686671356256941)
                    ·
                      rfl

theorem cell22_1253468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_1253468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1253468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1253468 prefixEnd_1253468 := by exact prefixLift 1253468
  have htrace : WordTrace (prefixWord ++ tailWord_1253468) baseStart_1253468 baseEnd_1253468 := by
    simpa [prefixWord, tailWord_1253468, baseEnd_1253468] using wordTrace_append hprefix tailTrace_1253468
  have hstable : (prefixWord ++ tailWord_1253468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253468).length < 2 ^ (prefixWord ++ tailWord_1253468).sum := by decide
  have hdescent : baseEnd_1253468 < baseStart_1253468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
