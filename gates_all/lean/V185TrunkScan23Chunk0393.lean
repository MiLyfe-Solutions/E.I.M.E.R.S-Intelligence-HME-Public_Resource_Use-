import V185TrunkScan23Chunk0392

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2323097 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 3, 7]
def baseStart_2323097 : Nat := 118140960795 + 2323097 * 2 ^ 59
def prefixEnd_2323097 : Nat := 4983230072969 + 3 ^ 40 * 2323097 * 2
def baseEnd_2323097 : Nat := 397621789339334202001259

theorem tailTrace_2323097 : CollatzResearch.WordTrace tailWord_2323097 prefixEnd_2323097 397621789339334202001259 := by
  unfold tailWord_2323097
  simp only [CollatzResearch.WordTrace]
  refine ⟨84730308464823797225559545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56486872309882531483706363 84730308464823797225559545)
  ·
    refine ⟨63547731348617847919169659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84730308464823797225559545 63547731348617847919169659)
    ·
      refine ⟨95321597022926771878754489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63547731348617847919169659 95321597022926771878754489)
      ·
        refine ⟨71491197767195078909065867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95321597022926771878754489 71491197767195078909065867)
        ·
          refine ⟨107236796650792618363598801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71491197767195078909065867 107236796650792618363598801)
          ·
            refine ⟨80427597488094463772699101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107236796650792618363598801 80427597488094463772699101)
            ·
              refine ⟨30160349058035423914762163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80427597488094463772699101 30160349058035423914762163)
              ·
                refine ⟨45240523587053135872143245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30160349058035423914762163 45240523587053135872143245)
                ·
                  refine ⟨16965196345144925952053717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45240523587053135872143245 16965196345144925952053717)
                  ·
                    refine ⟨397621789339334202001259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16965196345144925952053717 397621789339334202001259)
                    ·
                      rfl

theorem cell23_2323097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 7].length) (baseStart_2323097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323097 prefixEnd_2323097 := by exact prefixLift 2323097
  have htrace : WordTrace (prefixWord ++ tailWord_2323097) baseStart_2323097 baseEnd_2323097 := by
    simpa [prefixWord, tailWord_2323097, baseEnd_2323097] using wordTrace_append hprefix tailTrace_2323097
  have hstable : (prefixWord ++ tailWord_2323097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323097).length < 2 ^ (prefixWord ++ tailWord_2323097).sum := by decide
  have hdescent : baseEnd_2323097 < baseStart_2323097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323107 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 7]
def baseStart_2323107 : Nat := 118140960795 + 2323107 * 2 ^ 59
def prefixEnd_2323107 : Nat := 4983230072969 + 3 ^ 40 * 2323107 * 2
def baseEnd_2323107 : Nat := 1192870502824547566878731

theorem tailTrace_2323107 : CollatzResearch.WordTrace tailWord_2323107 prefixEnd_2323107 1192870502824547566878731 := by
  unfold tailWord_2323107
  simp only [CollatzResearch.WordTrace]
  refine ⟨84730673194787568933423575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56487115463191712622282383 84730673194787568933423575)
  ·
    refine ⟨127096009792181353400135363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84730673194787568933423575 127096009792181353400135363)
    ·
      refine ⟨190644014688272030100203045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127096009792181353400135363 190644014688272030100203045)
      ·
        refine ⟨35745752754051005643788071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 190644014688272030100203045 35745752754051005643788071)
        ·
          refine ⟨53618629131076508465682107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35745752754051005643788071 53618629131076508465682107)
          ·
            refine ⟨80427943696614762698523161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53618629131076508465682107 80427943696614762698523161)
            ·
              refine ⟨60320957772461072023892371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80427943696614762698523161 60320957772461072023892371)
              ·
                refine ⟨90481436658691608035838557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60320957772461072023892371 90481436658691608035838557)
                ·
                  refine ⟨33930538747009353013439459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90481436658691608035838557 33930538747009353013439459)
                  ·
                    refine ⟨50895808120514029520159189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33930538747009353013439459 50895808120514029520159189)
                    ·
                      refine ⟨1192870502824547566878731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 50895808120514029520159189 1192870502824547566878731)
                      ·
                        rfl

theorem cell23_2323107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_2323107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323107 prefixEnd_2323107 := by exact prefixLift 2323107
  have htrace : WordTrace (prefixWord ++ tailWord_2323107) baseStart_2323107 baseEnd_2323107 := by
    simpa [prefixWord, tailWord_2323107, baseEnd_2323107] using wordTrace_append hprefix tailTrace_2323107
  have hstable : (prefixWord ++ tailWord_2323107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323107).length < 2 ^ (prefixWord ++ tailWord_2323107).sum := by decide
  have hdescent : baseEnd_2323107 < baseStart_2323107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323178 : List Nat := [3, 1, 3, 1, 1, 1, 1, 7, 1, 4]
def baseStart_2323178 : Nat := 118140960795 + 2323178 * 2 ^ 59
def prefixEnd_2323178 : Nat := 4983230072969 + 3 ^ 40 * 2323178 * 2
def baseEnd_2323178 : Nat := 397635653317005596363635

theorem tailTrace_2323178 : CollatzResearch.WordTrace tailWord_2323178 prefixEnd_2323178 397635653317005596363635 := by
  unfold tailWord_2323178
  simp only [CollatzResearch.WordTrace]
  refine ⟨21183315694382587014814547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56488841851686898706172125 21183315694382587014814547)
  ·
    refine ⟨31774973541573880522221821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21183315694382587014814547 31774973541573880522221821)
    ·
      refine ⟨11915615078090205195833183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31774973541573880522221821 11915615078090205195833183)
      ·
        refine ⟨17873422617135307793749775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11915615078090205195833183 17873422617135307793749775)
        ·
          refine ⟨26810133925702961690624663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17873422617135307793749775 26810133925702961690624663)
          ·
            refine ⟨40215200888554442535936995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26810133925702961690624663 40215200888554442535936995)
            ·
              refine ⟨60322801332831663803905493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40215200888554442535936995 60322801332831663803905493)
              ·
                refine ⟨1413815656238242120404035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 60322801332831663803905493 1413815656238242120404035)
                ·
                  refine ⟨2120723484357363180606053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1413815656238242120404035 2120723484357363180606053)
                  ·
                    refine ⟨397635653317005596363635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2120723484357363180606053 397635653317005596363635)
                    ·
                      rfl

theorem cell23_2323178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_2323178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323178 prefixEnd_2323178 := by exact prefixLift 2323178
  have htrace : WordTrace (prefixWord ++ tailWord_2323178) baseStart_2323178 baseEnd_2323178 := by
    simpa [prefixWord, tailWord_2323178, baseEnd_2323178] using wordTrace_append hprefix tailTrace_2323178
  have hstable : (prefixWord ++ tailWord_2323178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323178).length < 2 ^ (prefixWord ++ tailWord_2323178).sum := by decide
  have hdescent : baseEnd_2323178 < baseStart_2323178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323211 : List Nat := [1, 1, 1, 1, 5, 1, 1, 4, 1, 5, 2]
def baseStart_2323211 : Nat := 118140960795 + 2323211 * 2 ^ 59
def prefixEnd_2323211 : Nat := 4983230072969 + 3 ^ 40 * 2323211 * 2
def baseEnd_2323211 : Nat := 1192923904812615159978253

theorem tailTrace_2323211 : CollatzResearch.WordTrace tailWord_2323211 prefixEnd_2323211 1192923904812615159978253 := by
  unfold tailWord_2323211
  simp only [CollatzResearch.WordTrace]
  refine ⟨84734466386410794695209487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56489644257607196463472991 84734466386410794695209487)
  ·
    refine ⟨127101699579616192042814231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84734466386410794695209487 127101699579616192042814231)
    ·
      refine ⟨190652549369424288064221347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127101699579616192042814231 190652549369424288064221347)
      ·
        refine ⟨285978824054136432096332021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190652549369424288064221347 285978824054136432096332021)
        ·
          refine ⟨26810514755075290509031127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 285978824054136432096332021 26810514755075290509031127)
          ·
            refine ⟨40215772132612935763546691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26810514755075290509031127 40215772132612935763546691)
            ·
              refine ⟨60323658198919403645320037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40215772132612935763546691 60323658198919403645320037)
              ·
                refine ⟨11310685912297388183497507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60323658198919403645320037 11310685912297388183497507)
                ·
                  refine ⟨16966028868446082275246261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11310685912297388183497507 16966028868446082275246261)
                  ·
                    refine ⟨1590565206416820213304337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16966028868446082275246261 1590565206416820213304337)
                    ·
                      refine ⟨1192923904812615159978253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1590565206416820213304337 1192923904812615159978253)
                      ·
                        rfl

theorem cell23_2323211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 5, 2].length) (baseStart_2323211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323211 prefixEnd_2323211 := by exact prefixLift 2323211
  have htrace : WordTrace (prefixWord ++ tailWord_2323211) baseStart_2323211 baseEnd_2323211 := by
    simpa [prefixWord, tailWord_2323211, baseEnd_2323211] using wordTrace_append hprefix tailTrace_2323211
  have hstable : (prefixWord ++ tailWord_2323211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323211).length < 2 ^ (prefixWord ++ tailWord_2323211).sum := by decide
  have hdescent : baseEnd_2323211 < baseStart_2323211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323214 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7]
def baseStart_2323214 : Nat := 118140960795 + 2323214 * 2 ^ 59
def prefixEnd_2323214 : Nat := 4983230072969 + 3 ^ 40 * 2323214 * 2
def baseEnd_2323214 : Nat := 1192925445254578648240739

theorem tailTrace_2323214 : CollatzResearch.WordTrace tailWord_2323214 prefixEnd_2323214 1192925445254578648240739 := by
  unfold tailWord_2323214
  simp only [CollatzResearch.WordTrace]
  refine ⟨10591821975674990775946087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56489717203599950805045797 10591821975674990775946087)
  ·
    refine ⟨15887732963512486163919131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10591821975674990775946087 15887732963512486163919131)
    ·
      refine ⟨23831599445268729245878697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15887732963512486163919131 23831599445268729245878697)
      ·
        refine ⟨17873699583951546934409023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23831599445268729245878697 17873699583951546934409023)
        ·
          refine ⟨26810549375927320401613535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17873699583951546934409023 26810549375927320401613535)
          ·
            refine ⟨40215824063890980602420303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26810549375927320401613535 40215824063890980602420303)
            ·
              refine ⟨60323736095836470903630455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40215824063890980602420303 60323736095836470903630455)
              ·
                refine ⟨90485604143754706355445683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60323736095836470903630455 90485604143754706355445683)
                ·
                  refine ⟨135728406215632059533168525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90485604143754706355445683 135728406215632059533168525)
                  ·
                    refine ⟨50898152330862022324938197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 135728406215632059533168525 50898152330862022324938197)
                    ·
                      refine ⟨1192925445254578648240739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 50898152330862022324938197 1192925445254578648240739)
                      ·
                        rfl

theorem cell23_2323214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_2323214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323214 prefixEnd_2323214 := by exact prefixLift 2323214
  have htrace : WordTrace (prefixWord ++ tailWord_2323214) baseStart_2323214 baseEnd_2323214 := by
    simpa [prefixWord, tailWord_2323214, baseEnd_2323214] using wordTrace_append hprefix tailTrace_2323214
  have hstable : (prefixWord ++ tailWord_2323214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323214).length < 2 ^ (prefixWord ++ tailWord_2323214).sum := by decide
  have hdescent : baseEnd_2323214 < baseStart_2323214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323221 : List Nat := [1, 3, 2, 1, 2, 2, 2, 4, 1, 5]
def baseStart_2323221 : Nat := 118140960795 + 2323221 * 2 ^ 59
def prefixEnd_2323221 : Nat := 4983230072969 + 3 ^ 40 * 2323221 * 2
def baseEnd_2323221 : Nat := 397643013206386706951069

theorem tailTrace_2323221 : CollatzResearch.WordTrace tailWord_2323221 prefixEnd_2323221 397643013206386706951069 := by
  unfold tailWord_2323221
  simp only [CollatzResearch.WordTrace]
  refine ⟨84734831116374566403073517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56489887410916377602049011 84734831116374566403073517)
  ·
    refine ⟨31775561668640462401152569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84734831116374566403073517 31775561668640462401152569)
    ·
      refine ⟨23831671251480346800864427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31775561668640462401152569 23831671251480346800864427)
      ·
        refine ⟨35747506877220520201296641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23831671251480346800864427 35747506877220520201296641)
        ·
          refine ⟨26810630157915390150972481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35747506877220520201296641 26810630157915390150972481)
          ·
            refine ⟨20107972618436542613229361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26810630157915390150972481 20107972618436542613229361)
            ·
              refine ⟨15080979463827406959922021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20107972618436542613229361 15080979463827406959922021)
              ·
                refine ⟨2827683649467638804985379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15080979463827406959922021 2827683649467638804985379)
                ·
                  refine ⟨4241525474201458207478069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2827683649467638804985379 4241525474201458207478069)
                  ·
                    refine ⟨397643013206386706951069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4241525474201458207478069 397643013206386706951069)
                    ·
                      rfl

theorem cell23_2323221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_2323221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323221 prefixEnd_2323221 := by exact prefixLift 2323221
  have htrace : WordTrace (prefixWord ++ tailWord_2323221) baseStart_2323221 baseEnd_2323221 := by
    simpa [prefixWord, tailWord_2323221, baseEnd_2323221] using wordTrace_append hprefix tailTrace_2323221
  have hstable : (prefixWord ++ tailWord_2323221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323221).length < 2 ^ (prefixWord ++ tailWord_2323221).sum := by decide
  have hdescent : baseEnd_2323221 < baseStart_2323221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323228 : List Nat := [2, 2, 3, 1, 1, 4, 1, 1, 1, 5, 2]
def baseStart_2323228 : Nat := 118140960795 + 2323228 * 2 ^ 59
def prefixEnd_2323228 : Nat := 4983230072969 + 3 ^ 40 * 2323228 * 2
def baseEnd_2323228 : Nat := 1192932633983741593465675

theorem tailTrace_2323228 : CollatzResearch.WordTrace tailWord_2323228 prefixEnd_2323228 1192932633983741593465675 := by
  unfold tailWord_2323228
  simp only [CollatzResearch.WordTrace]
  refine ⟨42367543213674603299289169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56490057618232804399052225 42367543213674603299289169)
  ·
    refine ⟨31775657410255952474466877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42367543213674603299289169 31775657410255952474466877)
    ·
      refine ⟨11915871528845982177925079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31775657410255952474466877 11915871528845982177925079)
      ·
        refine ⟨17873807293268973266887619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11915871528845982177925079 17873807293268973266887619)
        ·
          refine ⟨26810710939903459900331429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17873807293268973266887619 26810710939903459900331429)
          ·
            refine ⟨5027008301231898731312143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26810710939903459900331429 5027008301231898731312143)
            ·
              refine ⟨7540512451847848096968215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5027008301231898731312143 7540512451847848096968215)
              ·
                refine ⟨11310768677771772145452323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7540512451847848096968215 11310768677771772145452323)
                ·
                  refine ⟨16966153016657658218178485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11310768677771772145452323 16966153016657658218178485)
                  ·
                    refine ⟨1590576845311655457954233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16966153016657658218178485 1590576845311655457954233)
                    ·
                      refine ⟨1192932633983741593465675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1590576845311655457954233 1192932633983741593465675)
                      ·
                        rfl

theorem cell23_2323228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_2323228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323228 prefixEnd_2323228 := by exact prefixLift 2323228
  have htrace : WordTrace (prefixWord ++ tailWord_2323228) baseStart_2323228 baseEnd_2323228 := by
    simpa [prefixWord, tailWord_2323228, baseEnd_2323228] using wordTrace_append hprefix tailTrace_2323228
  have hstable : (prefixWord ++ tailWord_2323228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323228).length < 2 ^ (prefixWord ++ tailWord_2323228).sum := by decide
  have hdescent : baseEnd_2323228 < baseStart_2323228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323241 : List Nat := [1, 2, 1, 1, 1, 1, 1, 9, 1, 1, 4]
def baseStart_2323241 : Nat := 118140960795 + 2323241 * 2 ^ 59
def prefixEnd_2323241 : Nat := 4983230072969 + 3 ^ 40 * 2323241 * 2
def baseEnd_2323241 : Nat := 1192939309232250042603115

theorem tailTrace_2323241 : CollatzResearch.WordTrace tailWord_2323241 prefixEnd_2323241 1192939309232250042603115 := by
  unfold tailWord_2323241
  simp only [CollatzResearch.WordTrace]
  refine ⟨84735560576302109818801577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56490373717534739879201051 84735560576302109818801577)
  ·
    refine ⟨63551670432226582364101183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84735560576302109818801577 63551670432226582364101183)
    ·
      refine ⟨95327505648339873546151775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63551670432226582364101183 95327505648339873546151775)
      ·
        refine ⟨142991258472509810319227663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95327505648339873546151775 142991258472509810319227663)
        ·
          refine ⟨214486887708764715478841495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142991258472509810319227663 214486887708764715478841495)
          ·
            refine ⟨321730331563147073218262243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214486887708764715478841495 321730331563147073218262243)
            ·
              refine ⟨482595497344720609827393365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321730331563147073218262243 482595497344720609827393365)
              ·
                refine ⟨2827707992254222323207383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 482595497344720609827393365 2827707992254222323207383)
                ·
                  refine ⟨4241561988381333484811075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2827707992254222323207383 4241561988381333484811075)
                  ·
                    refine ⟨6362342982572000227216613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4241561988381333484811075 6362342982572000227216613)
                    ·
                      refine ⟨1192939309232250042603115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6362342982572000227216613 1192939309232250042603115)
                      ·
                        rfl

theorem cell23_2323241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 1, 4].length) (baseStart_2323241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323241 prefixEnd_2323241 := by exact prefixLift 2323241
  have htrace : WordTrace (prefixWord ++ tailWord_2323241) baseStart_2323241 baseEnd_2323241 := by
    simpa [prefixWord, tailWord_2323241, baseEnd_2323241] using wordTrace_append hprefix tailTrace_2323241
  have hstable : (prefixWord ++ tailWord_2323241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323241).length < 2 ^ (prefixWord ++ tailWord_2323241).sum := by decide
  have hdescent : baseEnd_2323241 < baseStart_2323241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323242 : List Nat := [3, 1, 4, 3, 2, 1, 1, 2, 6]
def baseStart_2323242 : Nat := 118140960795 + 2323242 * 2 ^ 59
def prefixEnd_2323242 : Nat := 4983230072969 + 3 ^ 40 * 2323242 * 2
def baseEnd_2323242 : Nat := 132548869190322726521179

theorem tailTrace_2323242 : CollatzResearch.WordTrace tailWord_2323242 prefixEnd_2323242 132548869190322726521179 := by
  unfold tailWord_2323242
  simp only [CollatzResearch.WordTrace]
  refine ⟨21183899262324621747396995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56490398032865657993058653 21183899262324621747396995)
  ·
    refine ⟨31775848893486932621095493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21183899262324621747396995 31775848893486932621095493)
    ·
      refine ⟨5957971667528799866455405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31775848893486932621095493 5957971667528799866455405)
      ·
        refine ⟨2234239375323299949920777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5957971667528799866455405 2234239375323299949920777)
        ·
          refine ⟨1675679531492474962440583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2234239375323299949920777 1675679531492474962440583)
          ·
            refine ⟨2513519297238712443660875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1675679531492474962440583 2513519297238712443660875)
            ·
              refine ⟨3770278945858068665491313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2513519297238712443660875 3770278945858068665491313)
              ·
                refine ⟨2827709209393551499118485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3770278945858068665491313 2827709209393551499118485)
                ·
                  refine ⟨132548869190322726521179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2827709209393551499118485 132548869190322726521179)
                  ·
                    rfl

theorem cell23_2323242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 6].length) (baseStart_2323242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323242 prefixEnd_2323242 := by exact prefixLift 2323242
  have htrace : WordTrace (prefixWord ++ tailWord_2323242) baseStart_2323242 baseEnd_2323242 := by
    simpa [prefixWord, tailWord_2323242, baseEnd_2323242] using wordTrace_append hprefix tailTrace_2323242
  have hstable : (prefixWord ++ tailWord_2323242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323242).length < 2 ^ (prefixWord ++ tailWord_2323242).sum := by decide
  have hdescent : baseEnd_2323242 < baseStart_2323242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323252 : List Nat := [2, 5, 1, 1, 3, 1, 2, 1, 3, 1, 3]
def baseStart_2323252 : Nat := 118140960795 + 2323252 * 2 ^ 59
def prefixEnd_2323252 : Nat := 4983230072969 + 3 ^ 40 * 2323252 * 2
def baseEnd_2323252 : Nat := 1192944957519449499565565

theorem tailTrace_2323252 : CollatzResearch.WordTrace tailWord_2323252 prefixEnd_2323252 1192944957519449499565565 := by
  unfold tailWord_2323252
  simp only [CollatzResearch.WordTrace]
  refine ⟨42367980889631129348726005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56490641186174839131634673 42367980889631129348726005)
  ·
    refine ⟨3971998208402918376443063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42367980889631129348726005 3971998208402918376443063)
    ·
      refine ⟨5957997312604377564664595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3971998208402918376443063 5957997312604377564664595)
      ·
        refine ⟨8936995968906566346996893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5957997312604377564664595 8936995968906566346996893)
        ·
          refine ⟨3351373488339962380123835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8936995968906566346996893 3351373488339962380123835)
          ·
            refine ⟨5027060232509943570185753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3351373488339962380123835 5027060232509943570185753)
            ·
              refine ⟨3770295174382457677639315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5027060232509943570185753 3770295174382457677639315)
              ·
                refine ⟨5655442761573686516458973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3770295174382457677639315 5655442761573686516458973)
                ·
                  refine ⟨2120791035590132443672115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5655442761573686516458973 2120791035590132443672115)
                  ·
                    refine ⟨3181186553385198665508173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2120791035590132443672115 3181186553385198665508173)
                    ·
                      refine ⟨1192944957519449499565565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3181186553385198665508173 1192944957519449499565565)
                      ·
                        rfl

theorem cell23_2323252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_2323252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323252 prefixEnd_2323252 := by exact prefixLift 2323252
  have htrace : WordTrace (prefixWord ++ tailWord_2323252) baseStart_2323252 baseEnd_2323252 := by
    simpa [prefixWord, tailWord_2323252, baseEnd_2323252] using wordTrace_append hprefix tailTrace_2323252
  have hstable : (prefixWord ++ tailWord_2323252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323252).length < 2 ^ (prefixWord ++ tailWord_2323252).sum := by decide
  have hdescent : baseEnd_2323252 < baseStart_2323252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323281 : List Nat := [1, 2, 2, 1, 6, 1, 1, 9]
def baseStart_2323281 : Nat := 118140960795 + 2323281 * 2 ^ 59
def prefixEnd_2323281 : Nat := 4983230072969 + 3 ^ 40 * 2323281 * 2
def baseEnd_2323281 : Nat := 44183698091052958744553

theorem tailTrace_2323281 : CollatzResearch.WordTrace tailWord_2323281 prefixEnd_2323281 44183698091052958744553 := by
  unfold tailWord_2323281
  simp only [CollatzResearch.WordTrace]
  refine ⟨84737019496157196650257697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56491346330771464433505131 84737019496157196650257697)
  ·
    refine ⟨63552764622117897487693273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84737019496157196650257697 63552764622117897487693273)
    ·
      refine ⟨47664573466588423115769955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63552764622117897487693273 47664573466588423115769955)
      ·
        refine ⟨71496860199882634673654933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47664573466588423115769955 71496860199882634673654933)
        ·
          refine ⟨3351415321869498500327575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 71496860199882634673654933 3351415321869498500327575)
          ·
            refine ⟨5027122982804247750491363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3351415321869498500327575 5027122982804247750491363)
            ·
              refine ⟨7540684474206371625737045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5027122982804247750491363 7540684474206371625737045)
              ·
                refine ⟨44183698091052958744553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7540684474206371625737045 44183698091052958744553)
                ·
                  rfl

theorem cell23_2323281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 9].length) (baseStart_2323281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323281 prefixEnd_2323281 := by exact prefixLift 2323281
  have htrace : WordTrace (prefixWord ++ tailWord_2323281) baseStart_2323281 baseEnd_2323281 := by
    simpa [prefixWord, tailWord_2323281, baseEnd_2323281] using wordTrace_append hprefix tailTrace_2323281
  have hstable : (prefixWord ++ tailWord_2323281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323281).length < 2 ^ (prefixWord ++ tailWord_2323281).sum := by decide
  have hdescent : baseEnd_2323281 < baseStart_2323281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323298 : List Nat := [3, 3, 2, 1, 3, 2, 9]
def baseStart_2323298 : Nat := 118140960795 + 2323298 * 2 ^ 59
def prefixEnd_2323298 : Nat := 4983230072969 + 3 ^ 40 * 2323298 * 2
def baseEnd_2323298 : Nat := 14728007131229090365313

theorem tailTrace_2323298 : CollatzResearch.WordTrace tailWord_2323298 prefixEnd_2323298 14728007131229090365313 := by
  unfold tailWord_2323298
  simp only [CollatzResearch.WordTrace]
  refine ⟨21184409884273902138406637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56491759691397072369084365 21184409884273902138406637)
  ·
    refine ⟨7944153706602713301902489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21184409884273902138406637 7944153706602713301902489)
    ·
      refine ⟨5958115279952034976426867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7944153706602713301902489 5958115279952034976426867)
      ·
        refine ⟨8937172919928052464640301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5958115279952034976426867 8937172919928052464640301)
        ·
          refine ⟨3351439844973019674240113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8937172919928052464640301 3351439844973019674240113)
          ·
            refine ⟨2513579883729764755680085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3351439844973019674240113 2513579883729764755680085)
            ·
              refine ⟨14728007131229090365313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2513579883729764755680085 14728007131229090365313)
              ·
                rfl

theorem cell23_2323298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 9].length) (baseStart_2323298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323298 prefixEnd_2323298 := by exact prefixLift 2323298
  have htrace : WordTrace (prefixWord ++ tailWord_2323298) baseStart_2323298 baseEnd_2323298 := by
    simpa [prefixWord, tailWord_2323298, baseEnd_2323298] using wordTrace_append hprefix tailTrace_2323298
  have hstable : (prefixWord ++ tailWord_2323298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323298).length < 2 ^ (prefixWord ++ tailWord_2323298).sum := by decide
  have hdescent : baseEnd_2323298 < baseStart_2323298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323308 : List Nat := [2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 3]
def baseStart_2323308 : Nat := 118140960795 + 2323308 * 2 ^ 59
def prefixEnd_2323308 : Nat := 4983230072969 + 3 ^ 40 * 2323308 * 2
def baseEnd_2323308 : Nat := 1192973712436101280465307

theorem tailTrace_2323308 : CollatzResearch.WordTrace tailWord_2323308 prefixEnd_2323308 1192973712436101280465307 := by
  unfold tailWord_2323308
  simp only [CollatzResearch.WordTrace]
  refine ⟨42369002133529690130745289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56492002844706253507660385 42369002133529690130745289)
  ·
    refine ⟨31776751600147267598058967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42369002133529690130745289 31776751600147267598058967)
    ·
      refine ⟨47665127400220901397088451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31776751600147267598058967 47665127400220901397088451)
      ·
        refine ⟨71497691100331352095632677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47665127400220901397088451 71497691100331352095632677)
        ·
          refine ⟨13405817081312128517931127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71497691100331352095632677 13405817081312128517931127)
          ·
            refine ⟨20108725621968192776896691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13405817081312128517931127 20108725621968192776896691)
            ·
              refine ⟨30163088432952289165345037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20108725621968192776896691 30163088432952289165345037)
              ·
                refine ⟨11311158162357108437004389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30163088432952289165345037 11311158162357108437004389)
                ·
                  refine ⟨2120842155441957831938323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11311158162357108437004389 2120842155441957831938323)
                  ·
                    refine ⟨3181263233162936747907485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2120842155441957831938323 3181263233162936747907485)
                    ·
                      refine ⟨1192973712436101280465307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3181263233162936747907485 1192973712436101280465307)
                      ·
                        rfl

theorem cell23_2323308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 3].length) (baseStart_2323308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323308 prefixEnd_2323308 := by exact prefixLift 2323308
  have htrace : WordTrace (prefixWord ++ tailWord_2323308) baseStart_2323308 baseEnd_2323308 := by
    simpa [prefixWord, tailWord_2323308, baseEnd_2323308] using wordTrace_append hprefix tailTrace_2323308
  have hstable : (prefixWord ++ tailWord_2323308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323308).length < 2 ^ (prefixWord ++ tailWord_2323308).sum := by decide
  have hdescent : baseEnd_2323308 < baseStart_2323308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323335 : List Nat := [1, 1, 4, 2, 3, 2, 1, 1, 3, 3, 2]
def baseStart_2323335 : Nat := 118140960795 + 2323335 * 2 ^ 59
def prefixEnd_2323335 : Nat := 4983230072969 + 3 ^ 40 * 2323335 * 2
def baseEnd_2323335 : Nat := 1192987576413772674827683

theorem tailTrace_2323335 : CollatzResearch.WordTrace tailWord_2323335 prefixEnd_2323335 1192987576413772674827683 := by
  unfold tailWord_2323335
  simp only [CollatzResearch.WordTrace]
  refine ⟨84738989037961563872723459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56492659358641042581815639 84738989037961563872723459)
  ·
    refine ⟨127108483556942345809085189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84738989037961563872723459 127108483556942345809085189)
    ·
      refine ⟨23832840666926689839203473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127108483556942345809085189 23832840666926689839203473)
      ·
        refine ⟨17874630500195017379402605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23832840666926689839203473 17874630500195017379402605)
        ·
          refine ⟨6702986437573131517275977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17874630500195017379402605 6702986437573131517275977)
          ·
            refine ⟨5027239828179848637956983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6702986437573131517275977 5027239828179848637956983)
            ·
              refine ⟨7540859742269772956935475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5027239828179848637956983 7540859742269772956935475)
              ·
                refine ⟨11311289613404659435403213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7540859742269772956935475 11311289613404659435403213)
                ·
                  refine ⟨4241733605026747288276205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11311289613404659435403213 4241733605026747288276205)
                  ·
                    refine ⟨1590650101885030233103577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4241733605026747288276205 1590650101885030233103577)
                    ·
                      refine ⟨1192987576413772674827683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1590650101885030233103577 1192987576413772674827683)
                      ·
                        rfl

theorem cell23_2323335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_2323335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323335 prefixEnd_2323335 := by exact prefixLift 2323335
  have htrace : WordTrace (prefixWord ++ tailWord_2323335) baseStart_2323335 baseEnd_2323335 := by
    simpa [prefixWord, tailWord_2323335, baseEnd_2323335] using wordTrace_append hprefix tailTrace_2323335
  have hstable : (prefixWord ++ tailWord_2323335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323335).length < 2 ^ (prefixWord ++ tailWord_2323335).sum := by decide
  have hdescent : baseEnd_2323335 < baseStart_2323335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323351 : List Nat := [1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 5]
def baseStart_2323351 : Nat := 118140960795 + 2323351 * 2 ^ 59
def prefixEnd_2323351 : Nat := 4983230072969 + 3 ^ 40 * 2323351 * 2
def baseEnd_2323351 : Nat := 1192995792104244612227609

theorem tailTrace_2323351 : CollatzResearch.WordTrace tailWord_2323351 prefixEnd_2323351 1192995792104244612227609 := by
  unfold tailWord_2323351
  simp only [CollatzResearch.WordTrace]
  refine ⟨84739572605903598605305907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56493048403935732403537271 84739572605903598605305907)
  ·
    refine ⟨127109358908855397907958861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84739572605903598605305907 127109358908855397907958861)
    ·
      refine ⟨47666009590820774215484573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127109358908855397907958861 47666009590820774215484573)
      ·
        refine ⟨17874753596557790330806715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47666009590820774215484573 17874753596557790330806715)
        ·
          refine ⟨26812130394836685496210073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17874753596557790330806715 26812130394836685496210073)
          ·
            refine ⟨20109097796127514122157555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26812130394836685496210073 20109097796127514122157555)
            ·
              refine ⟨30163646694191271183236333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20109097796127514122157555 30163646694191271183236333)
              ·
                refine ⟨11311367510321726693713625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30163646694191271183236333 11311367510321726693713625)
                ·
                  refine ⟨8483525632741295020285219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11311367510321726693713625 8483525632741295020285219)
                  ·
                    refine ⟨12725288449111942530427829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8483525632741295020285219 12725288449111942530427829)
                    ·
                      refine ⟨1192995792104244612227609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12725288449111942530427829 1192995792104244612227609)
                      ·
                        rfl

theorem cell23_2323351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_2323351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323351 prefixEnd_2323351 := by exact prefixLift 2323351
  have htrace : WordTrace (prefixWord ++ tailWord_2323351) baseStart_2323351 baseEnd_2323351 := by
    simpa [prefixWord, tailWord_2323351, baseEnd_2323351] using wordTrace_append hprefix tailTrace_2323351
  have hstable : (prefixWord ++ tailWord_2323351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323351).length < 2 ^ (prefixWord ++ tailWord_2323351).sum := by decide
  have hdescent : baseEnd_2323351 < baseStart_2323351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323451 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 4]
def baseStart_2323451 : Nat := 118140960795 + 2323451 * 2 ^ 59
def prefixEnd_2323451 : Nat := 4983230072969 + 3 ^ 40 * 2323451 * 2
def baseEnd_2323451 : Nat := 1193047140169694220977149

theorem tailTrace_2323451 : CollatzResearch.WordTrace tailWord_2323451 prefixEnd_2323451 1193047140169694220977149 := by
  unfold tailWord_2323451
  simp only [CollatzResearch.WordTrace]
  refine ⟨84743219905541315683946207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56495479937027543789297471 84743219905541315683946207)
  ·
    refine ⟨127114829858311973525919311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84743219905541315683946207 127114829858311973525919311)
    ·
      refine ⟨190672244787467960288878967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127114829858311973525919311 190672244787467960288878967)
      ·
        refine ⟨286008367181201940433318451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190672244787467960288878967 286008367181201940433318451)
        ·
          refine ⟨429012550771802910649977677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286008367181201940433318451 429012550771802910649977677)
          ·
            refine ⟨160879706539426091493741629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 429012550771802910649977677 160879706539426091493741629)
            ·
              refine ⟨60329889952284784310153111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 160879706539426091493741629 60329889952284784310153111)
              ·
                refine ⟨90494834928427176465229667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60329889952284784310153111 90494834928427176465229667)
                ·
                  refine ⟨135742252392640764697844501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90494834928427176465229667 135742252392640764697844501)
                  ·
                    refine ⟨6362918080905035845211461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 135742252392640764697844501 6362918080905035845211461)
                    ·
                      refine ⟨1193047140169694220977149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6362918080905035845211461 1193047140169694220977149)
                      ·
                        rfl

theorem cell23_2323451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 4].length) (baseStart_2323451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323451 prefixEnd_2323451 := by exact prefixLift 2323451
  have htrace : WordTrace (prefixWord ++ tailWord_2323451) baseStart_2323451 baseEnd_2323451 := by
    simpa [prefixWord, tailWord_2323451, baseEnd_2323451] using wordTrace_append hprefix tailTrace_2323451
  have hstable : (prefixWord ++ tailWord_2323451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323451).length < 2 ^ (prefixWord ++ tailWord_2323451).sum := by decide
  have hdescent : baseEnd_2323451 < baseStart_2323451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323461 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 10]
def baseStart_2323461 : Nat := 118140960795 + 2323461 * 2 ^ 59
def prefixEnd_2323461 : Nat := 4983230072969 + 3 ^ 40 * 2323461 * 2
def baseEnd_2323461 : Nat := 132561363886248797983567

theorem tailTrace_2323461 : CollatzResearch.WordTrace tailWord_2323461 prefixEnd_2323461 132561363886248797983567 := by
  unfold tailWord_2323461
  simp only [CollatzResearch.WordTrace]
  refine ⟨84743584635505087391810237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56495723090336724927873491 84743584635505087391810237)
  ·
    refine ⟨31778844238314407771928839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84743584635505087391810237 31778844238314407771928839)
    ·
      refine ⟨47668266357471611657893259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31778844238314407771928839 47668266357471611657893259)
      ·
        refine ⟨71502399536207417486839889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47668266357471611657893259 71502399536207417486839889)
        ·
          refine ⟨53626799652155563115129917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71502399536207417486839889 53626799652155563115129917)
          ·
            refine ⟨20110049869558336168173719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53626799652155563115129917 20110049869558336168173719)
            ·
              refine ⟨30165074804337504252260579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20110049869558336168173719 30165074804337504252260579)
              ·
                refine ⟨45247612206506256378390869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30165074804337504252260579 45247612206506256378390869)
                ·
                  refine ⟨132561363886248797983567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 45247612206506256378390869 132561363886248797983567)
                  ·
                    rfl

theorem cell23_2323461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 10].length) (baseStart_2323461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323461 prefixEnd_2323461 := by exact prefixLift 2323461
  have htrace : WordTrace (prefixWord ++ tailWord_2323461) baseStart_2323461 baseEnd_2323461 := by
    simpa [prefixWord, tailWord_2323461, baseEnd_2323461] using wordTrace_append hprefix tailTrace_2323461
  have hstable : (prefixWord ++ tailWord_2323461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323461).length < 2 ^ (prefixWord ++ tailWord_2323461).sum := by decide
  have hdescent : baseEnd_2323461 < baseStart_2323461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323481 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 1, 1, 8]
def baseStart_2323481 : Nat := 118140960795 + 2323481 * 2 ^ 59
def prefixEnd_2323481 : Nat := 4983230072969 + 3 ^ 40 * 2323481 * 2
def baseEnd_2323481 : Nat := 1193062544589329103602011

theorem tailTrace_2323481 : CollatzResearch.WordTrace tailWord_2323481 prefixEnd_2323481 1193062544589329103602011 := by
  unfold tailWord_2323481
  simp only [CollatzResearch.WordTrace]
  refine ⟨84744314095432630807538297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56496209396955087205025531 84744314095432630807538297)
  ·
    refine ⟨63558235571574473105653723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84744314095432630807538297 63558235571574473105653723)
    ·
      refine ⟨95337353357361709658480585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63558235571574473105653723 95337353357361709658480585)
      ·
        refine ⟨71503015018021282243860439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95337353357361709658480585 71503015018021282243860439)
        ·
          refine ⟨107254522527031923365790659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71503015018021282243860439 107254522527031923365790659)
          ·
            refine ⟨160881783790547885048685989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107254522527031923365790659 160881783790547885048685989)
            ·
              refine ⟨30165334460727728446628623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 160881783790547885048685989 30165334460727728446628623)
              ·
                refine ⟨45248001691091592669942935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30165334460727728446628623 45248001691091592669942935)
                ·
                  refine ⟨67872002536637389004914403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45248001691091592669942935 67872002536637389004914403)
                  ·
                    refine ⟨101808003804956083507371605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67872002536637389004914403 101808003804956083507371605)
                    ·
                      refine ⟨1193062544589329103602011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 101808003804956083507371605 1193062544589329103602011)
                      ·
                        rfl

theorem cell23_2323481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_2323481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323481 prefixEnd_2323481 := by exact prefixLift 2323481
  have htrace : WordTrace (prefixWord ++ tailWord_2323481) baseStart_2323481 baseEnd_2323481 := by
    simpa [prefixWord, tailWord_2323481, baseEnd_2323481] using wordTrace_append hprefix tailTrace_2323481
  have hstable : (prefixWord ++ tailWord_2323481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323481).length < 2 ^ (prefixWord ++ tailWord_2323481).sum := by decide
  have hdescent : baseEnd_2323481 < baseStart_2323481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323505 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 5, 1, 3]
def baseStart_2323505 : Nat := 118140960795 + 2323505 * 2 ^ 59
def prefixEnd_2323505 : Nat := 4983230072969 + 3 ^ 40 * 2323505 * 2
def baseEnd_2323505 : Nat := 1193074868125037009701901

theorem tailTrace_2323505 : CollatzResearch.WordTrace tailWord_2323505 prefixEnd_2323505 1193074868125037009701901 := by
  unfold tailWord_2323505
  simp only [CollatzResearch.WordTrace]
  refine ⟨84745189447345682906411969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56496792964897121937607979 84745189447345682906411969)
  ·
    refine ⟨63558892085509262179808977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84745189447345682906411969 63558892085509262179808977)
    ·
      refine ⟨47669169064131946634856733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63558892085509262179808977 47669169064131946634856733)
      ·
        refine ⟨17875938399049479988071275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47669169064131946634856733 17875938399049479988071275)
        ·
          refine ⟨26813907598574219982106913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17875938399049479988071275 26813907598574219982106913)
          ·
            refine ⟨20110430698930664986580185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26813907598574219982106913 20110430698930664986580185)
            ·
              refine ⟨15082823024197998739935139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20110430698930664986580185 15082823024197998739935139)
              ·
                refine ⟨22624234536296998109902709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15082823024197998739935139 22624234536296998109902709)
                ·
                  refine ⟨2121021987777843572803379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22624234536296998109902709 2121021987777843572803379)
                  ·
                    refine ⟨3181532981666765359205069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2121021987777843572803379 3181532981666765359205069)
                    ·
                      refine ⟨1193074868125037009701901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3181532981666765359205069 1193074868125037009701901)
                      ·
                        rfl

theorem cell23_2323505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_2323505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323505 prefixEnd_2323505 := by exact prefixLift 2323505
  have htrace : WordTrace (prefixWord ++ tailWord_2323505) baseStart_2323505 baseEnd_2323505 := by
    simpa [prefixWord, tailWord_2323505, baseEnd_2323505] using wordTrace_append hprefix tailTrace_2323505
  have hstable : (prefixWord ++ tailWord_2323505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323505).length < 2 ^ (prefixWord ++ tailWord_2323505).sum := by decide
  have hdescent : baseEnd_2323505 < baseStart_2323505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323573 : List Nat := [1, 3, 4, 3, 1, 1, 2, 3, 1, 1, 3]
def baseStart_2323573 : Nat := 118140960795 + 2323573 * 2 ^ 59
def prefixEnd_2323573 : Nat := 4983230072969 + 3 ^ 40 * 2323573 * 2
def baseEnd_2323573 : Nat := 1193109784809542743651589

theorem tailTrace_2323573 : CollatzResearch.WordTrace tailWord_2323573 prefixEnd_2323573 1193109784809542743651589 := by
  unfold tailWord_2323573
  simp only [CollatzResearch.WordTrace]
  refine ⟨84747669611099330519887373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56498446407399553679924915 84747669611099330519887373)
  ·
    refine ⟨31780376104162248944957765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84747669611099330519887373 31780376104162248944957765)
    ·
      refine ⟨5958820519530421677179581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31780376104162248944957765 5958820519530421677179581)
      ·
        refine ⟨2234557694823908128942343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5958820519530421677179581 2234557694823908128942343)
        ·
          refine ⟨3351836542235862193413515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2234557694823908128942343 3351836542235862193413515)
          ·
            refine ⟨5027754813353793290120273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3351836542235862193413515 5027754813353793290120273)
            ·
              refine ⟨3770816110015344967590205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5027754813353793290120273 3770816110015344967590205)
              ·
                refine ⟨1414056041255754362846327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3770816110015344967590205 1414056041255754362846327)
                ·
                  refine ⟨2121084061883631544269491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1414056041255754362846327 2121084061883631544269491)
                  ·
                    refine ⟨3181626092825447316404237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2121084061883631544269491 3181626092825447316404237)
                    ·
                      refine ⟨1193109784809542743651589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3181626092825447316404237 1193109784809542743651589)
                      ·
                        rfl

theorem cell23_2323573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_2323573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323573 prefixEnd_2323573 := by exact prefixLift 2323573
  have htrace : WordTrace (prefixWord ++ tailWord_2323573) baseStart_2323573 baseEnd_2323573 := by
    simpa [prefixWord, tailWord_2323573, baseEnd_2323573] using wordTrace_append hprefix tailTrace_2323573
  have hstable : (prefixWord ++ tailWord_2323573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323573).length < 2 ^ (prefixWord ++ tailWord_2323573).sum := by decide
  have hdescent : baseEnd_2323573 < baseStart_2323573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323589 : List Nat := [1, 3, 1, 1, 6, 2, 1, 2, 2, 4]
def baseStart_2323589 : Nat := 118140960795 + 2323589 * 2 ^ 59
def prefixEnd_2323589 : Nat := 4983230072969 + 3 ^ 40 * 2323589 * 2
def baseEnd_2323589 : Nat := 397706000166671560350505

theorem tailTrace_2323589 : CollatzResearch.WordTrace tailWord_2323589 prefixEnd_2323589 397706000166671560350505 := by
  unfold tailWord_2323589
  simp only [CollatzResearch.WordTrace]
  refine ⟨84748253179041365252469821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56498835452694243501646547 84748253179041365252469821)
  ·
    refine ⟨31780594942140511969676183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84748253179041365252469821 31780594942140511969676183)
    ·
      refine ⟨47670892413210767954514275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31780594942140511969676183 47670892413210767954514275)
      ·
        refine ⟨71506338619816151931771413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47670892413210767954514275 71506338619816151931771413)
        ·
          refine ⟨3351859622803882121801785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 71506338619816151931771413 3351859622803882121801785)
          ·
            refine ⟨2513894717102911591351339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3351859622803882121801785 2513894717102911591351339)
            ·
              refine ⟨3770842075654367387027009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2513894717102911591351339 3770842075654367387027009)
              ·
                refine ⟨2828131556740775540270257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3770842075654367387027009 2828131556740775540270257)
                ·
                  refine ⟨2121098667555581655202693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2828131556740775540270257 2121098667555581655202693)
                  ·
                    refine ⟨397706000166671560350505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2121098667555581655202693 397706000166671560350505)
                    ·
                      rfl

theorem cell23_2323589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 2, 4].length) (baseStart_2323589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323589 prefixEnd_2323589 := by exact prefixLift 2323589
  have htrace : WordTrace (prefixWord ++ tailWord_2323589) baseStart_2323589 baseEnd_2323589 := by
    simpa [prefixWord, tailWord_2323589, baseEnd_2323589] using wordTrace_append hprefix tailTrace_2323589
  have hstable : (prefixWord ++ tailWord_2323589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323589).length < 2 ^ (prefixWord ++ tailWord_2323589).sum := by decide
  have hdescent : baseEnd_2323589 < baseStart_2323589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323605 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 2, 7, 2]
def baseStart_2323605 : Nat := 118140960795 + 2323605 * 2 ^ 59
def prefixEnd_2323605 : Nat := 4983230072969 + 3 ^ 40 * 2323605 * 2
def baseEnd_2323605 : Nat := 1193126216190486618451441

theorem tailTrace_2323605 : CollatzResearch.WordTrace tailWord_2323605 prefixEnd_2323605 1193126216190486618451441 := by
  unfold tailWord_2323605
  simp only [CollatzResearch.WordTrace]
  refine ⟨84748836746983399985052269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56499224497988933323368179 84748836746983399985052269)
  ·
    refine ⟨31780813780118774994394601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84748836746983399985052269 31780813780118774994394601)
    ·
      refine ⟨23835610335089081245795951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31780813780118774994394601 23835610335089081245795951)
      ·
        refine ⟨35753415502633621868693927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23835610335089081245795951 35753415502633621868693927)
        ·
          refine ⟨53630123253950432803040891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35753415502633621868693927 53630123253950432803040891)
          ·
            refine ⟨80445184880925649204561337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53630123253950432803040891 80445184880925649204561337)
            ·
              refine ⟨60333888660694236903421003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80445184880925649204561337 60333888660694236903421003)
              ·
                refine ⟨90500832991041355355131505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60333888660694236903421003 90500832991041355355131505)
                ·
                  refine ⟨67875624743281016516348629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90500832991041355355131505 67875624743281016516348629)
                  ·
                    refine ⟨1590834954920648824601921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 67875624743281016516348629 1590834954920648824601921)
                    ·
                      refine ⟨1193126216190486618451441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1590834954920648824601921 1193126216190486618451441)
                      ·
                        rfl

theorem cell23_2323605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 7, 2].length) (baseStart_2323605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323605 prefixEnd_2323605 := by exact prefixLift 2323605
  have htrace : WordTrace (prefixWord ++ tailWord_2323605) baseStart_2323605 baseEnd_2323605 := by
    simpa [prefixWord, tailWord_2323605, baseEnd_2323605] using wordTrace_append hprefix tailTrace_2323605
  have hstable : (prefixWord ++ tailWord_2323605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323605).length < 2 ^ (prefixWord ++ tailWord_2323605).sum := by decide
  have hdescent : baseEnd_2323605 < baseStart_2323605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323612 : List Nat := [2, 2, 3, 2, 1, 2, 3, 1, 1, 3, 3]
def baseStart_2323612 : Nat := 118140960795 + 2323612 * 2 ^ 59
def prefixEnd_2323612 : Nat := 4983230072969 + 3 ^ 40 * 2323612 * 2
def baseEnd_2323612 : Nat := 1193129810555068091063909

theorem tailTrace_2323612 : CollatzResearch.WordTrace tailWord_2323612 prefixEnd_2323612 1193129810555068091063909 := by
  unfold tailWord_2323612
  simp only [CollatzResearch.WordTrace]
  refine ⟨42374546028979020090278545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56499394705305360120371393 42374546028979020090278545)
  ·
    refine ⟨31780909521734265067708909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42374546028979020090278545 31780909521734265067708909)
    ·
      refine ⟨11917841070650349400390841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31780909521734265067708909 11917841070650349400390841)
      ·
        refine ⟨8938380802987762050293131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11917841070650349400390841 8938380802987762050293131)
        ·
          refine ⟨13407571204481643075439697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8938380802987762050293131 13407571204481643075439697)
          ·
            refine ⟨10055678403361232306579773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13407571204481643075439697 10055678403361232306579773)
            ·
              refine ⟨3770879401260462114967415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10055678403361232306579773 3770879401260462114967415)
              ·
                refine ⟨5656319101890693172451123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3770879401260462114967415 5656319101890693172451123)
                ·
                  refine ⟨8484478652836039758676685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5656319101890693172451123 8484478652836039758676685)
                  ·
                    refine ⟨3181679494813514909503757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8484478652836039758676685 3181679494813514909503757)
                    ·
                      refine ⟨1193129810555068091063909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3181679494813514909503757 1193129810555068091063909)
                      ·
                        rfl

theorem cell23_2323612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_2323612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323612 prefixEnd_2323612 := by exact prefixLift 2323612
  have htrace : WordTrace (prefixWord ++ tailWord_2323612) baseStart_2323612 baseEnd_2323612 := by
    simpa [prefixWord, tailWord_2323612, baseEnd_2323612] using wordTrace_append hprefix tailTrace_2323612
  have hstable : (prefixWord ++ tailWord_2323612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323612).length < 2 ^ (prefixWord ++ tailWord_2323612).sum := by decide
  have hdescent : baseEnd_2323612 < baseStart_2323612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323628 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 4, 6]
def baseStart_2323628 : Nat := 118140960795 + 2323628 * 2 ^ 59
def prefixEnd_2323628 : Nat := 4983230072969 + 3 ^ 40 * 2323628 * 2
def baseEnd_2323628 : Nat := 397712675415180009487945

theorem tailTrace_2323628 : CollatzResearch.WordTrace tailWord_2323628 prefixEnd_2323628 397712675415180009487945 := by
  unfold tailWord_2323628
  simp only [CollatzResearch.WordTrace]
  refine ⟨42374837812950037456569769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56499783750600049942093025 42374837812950037456569769)
  ·
    refine ⟨31781128359712528092427327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42374837812950037456569769 31781128359712528092427327)
    ·
      refine ⟨47671692539568792138640991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31781128359712528092427327 47671692539568792138640991)
      ·
        refine ⟨71507538809353188207961487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47671692539568792138640991 71507538809353188207961487)
        ·
          refine ⟨107261308214029782311942231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71507538809353188207961487 107261308214029782311942231)
          ·
            refine ⟨160891962321044673467913347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107261308214029782311942231 160891962321044673467913347)
            ·
              refine ⟨241337943481567010201870021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160891962321044673467913347 241337943481567010201870021)
              ·
                refine ⟨45250864402793814412850629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 241337943481567010201870021 45250864402793814412850629)
                ·
                  refine ⟨8484537075523840202409493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45250864402793814412850629 8484537075523840202409493)
                  ·
                    refine ⟨397712675415180009487945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8484537075523840202409493 397712675415180009487945)
                    ·
                      rfl

theorem cell23_2323628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 6].length) (baseStart_2323628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323628 prefixEnd_2323628 := by exact prefixLift 2323628
  have htrace : WordTrace (prefixWord ++ tailWord_2323628) baseStart_2323628 baseEnd_2323628 := by
    simpa [prefixWord, tailWord_2323628, baseEnd_2323628] using wordTrace_append hprefix tailTrace_2323628
  have hstable : (prefixWord ++ tailWord_2323628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323628).length < 2 ^ (prefixWord ++ tailWord_2323628).sum := by decide
  have hdescent : baseEnd_2323628 < baseStart_2323628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323702 : List Nat := [5, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3]
def baseStart_2323702 : Nat := 118140960795 + 2323702 * 2 ^ 59
def prefixEnd_2323702 : Nat := 4983230072969 + 3 ^ 40 * 2323702 * 2
def baseEnd_2323702 : Nat := 1193176023813972738938495

theorem tailTrace_2323702 : CollatzResearch.WordTrace tailWord_2323702 prefixEnd_2323702 1193176023813972738938495 := by
  unfold tailWord_2323702
  simp only [CollatzResearch.WordTrace]
  refine ⟨5297023414226999096958335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56501583085087990367555573 5297023414226999096958335)
  ·
    refine ⟨7945535121340498645437503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5297023414226999096958335 7945535121340498645437503)
    ·
      refine ⟨11918302682010747968156255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7945535121340498645437503 11918302682010747968156255)
      ·
        refine ⟨17877454023016121952234383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11918302682010747968156255 17877454023016121952234383)
        ·
          refine ⟨26816181034524182928351575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17877454023016121952234383 26816181034524182928351575)
          ·
            refine ⟨40224271551786274392527363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26816181034524182928351575 40224271551786274392527363)
            ·
              refine ⟨60336407327679411588791045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40224271551786274392527363 60336407327679411588791045)
              ·
                refine ⟨11313076373939889672898321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60336407327679411588791045 11313076373939889672898321)
                ·
                  refine ⟨8484807280454917254673741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11313076373939889672898321 8484807280454917254673741)
                  ·
                    refine ⟨3181802730170593970502653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8484807280454917254673741 3181802730170593970502653)
                    ·
                      refine ⟨1193176023813972738938495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3181802730170593970502653 1193176023813972738938495)
                      ·
                        rfl

theorem cell23_2323702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_2323702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323702 prefixEnd_2323702 := by exact prefixLift 2323702
  have htrace : WordTrace (prefixWord ++ tailWord_2323702) baseStart_2323702 baseEnd_2323702 := by
    simpa [prefixWord, tailWord_2323702, baseEnd_2323702] using wordTrace_append hprefix tailTrace_2323702
  have hstable : (prefixWord ++ tailWord_2323702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323702).length < 2 ^ (prefixWord ++ tailWord_2323702).sum := by decide
  have hdescent : baseEnd_2323702 < baseStart_2323702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323705 : List Nat := [1, 2, 1, 3, 1, 1, 3, 4, 2, 5]
def baseStart_2323705 : Nat := 118140960795 + 2323705 * 2 ^ 59
def prefixEnd_2323705 : Nat := 4983230072969 + 3 ^ 40 * 2323705 * 2
def baseEnd_2323705 : Nat := 397725854751978742400327

theorem tailTrace_2323705 : CollatzResearch.WordTrace tailWord_2323705 prefixEnd_2323705 397725854751978742400327 := by
  unfold tailWord_2323705
  simp only [CollatzResearch.WordTrace]
  refine ⟨84752484046621117063692569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56501656031080744709128379 84752484046621117063692569)
  ·
    refine ⟨63564363034965837797769427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84752484046621117063692569 63564363034965837797769427)
    ·
      refine ⟨95346544552448756696654141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63564363034965837797769427 95346544552448756696654141)
      ·
        refine ⟨35754954207168283761245303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95346544552448756696654141 35754954207168283761245303)
        ·
          refine ⟨53632431310752425641867955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35754954207168283761245303 53632431310752425641867955)
          ·
            refine ⟨80448646966128638462801933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53632431310752425641867955 80448646966128638462801933)
            ·
              refine ⟨30168242612298239423550725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80448646966128638462801933 30168242612298239423550725)
              ·
                refine ⟨5656545489805919891915761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30168242612298239423550725 5656545489805919891915761)
                ·
                  refine ⟨4242409117354439918936821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5656545489805919891915761 4242409117354439918936821)
                  ·
                    refine ⟨397725854751978742400327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4242409117354439918936821 397725854751978742400327)
                    ·
                      rfl

theorem cell23_2323705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 5].length) (baseStart_2323705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323705 prefixEnd_2323705 := by exact prefixLift 2323705
  have htrace : WordTrace (prefixWord ++ tailWord_2323705) baseStart_2323705 baseEnd_2323705 := by
    simpa [prefixWord, tailWord_2323705, baseEnd_2323705] using wordTrace_append hprefix tailTrace_2323705
  have hstable : (prefixWord ++ tailWord_2323705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323705).length < 2 ^ (prefixWord ++ tailWord_2323705).sum := by decide
  have hdescent : baseEnd_2323705 < baseStart_2323705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323715 : List Nat := [1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 5]
def baseStart_2323715 : Nat := 118140960795 + 2323715 * 2 ^ 59
def prefixEnd_2323715 : Nat := 4983230072969 + 3 ^ 40 * 2323715 * 2
def baseEnd_2323715 : Nat := 1193182699062481188075935

theorem tailTrace_2323715 : CollatzResearch.WordTrace tailWord_2323715 prefixEnd_2323715 1193182699062481188075935 := by
  unfold tailWord_2323715
  simp only [CollatzResearch.WordTrace]
  refine ⟨84752848776584888771556599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56501899184389925847704399 84752848776584888771556599)
  ·
    refine ⟨127129273164877333157334899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84752848776584888771556599 127129273164877333157334899)
    ·
      refine ⟨190693909747315999736002349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127129273164877333157334899 190693909747315999736002349)
      ·
        refine ⟨71510216155243499901000881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190693909747315999736002349 71510216155243499901000881)
        ·
          refine ⟨53632662116432624925750661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71510216155243499901000881 53632662116432624925750661)
          ·
            refine ⟨10056124146831117173578249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53632662116432624925750661 10056124146831117173578249)
            ·
              refine ⟨7542093110123337880183687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10056124146831117173578249 7542093110123337880183687)
              ·
                refine ⟨11313139665185006820275531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7542093110123337880183687 11313139665185006820275531)
                ·
                  refine ⟨16969709497777510230413297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11313139665185006820275531 16969709497777510230413297)
                  ·
                    refine ⟨12727282123333132672809973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16969709497777510230413297 12727282123333132672809973)
                    ·
                      refine ⟨1193182699062481188075935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12727282123333132672809973 1193182699062481188075935)
                      ·
                        rfl

theorem cell23_2323715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_2323715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323715 prefixEnd_2323715 := by exact prefixLift 2323715
  have htrace : WordTrace (prefixWord ++ tailWord_2323715) baseStart_2323715 baseEnd_2323715 := by
    simpa [prefixWord, tailWord_2323715, baseEnd_2323715] using wordTrace_append hprefix tailTrace_2323715
  have hstable : (prefixWord ++ tailWord_2323715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323715).length < 2 ^ (prefixWord ++ tailWord_2323715).sum := by decide
  have hdescent : baseEnd_2323715 < baseStart_2323715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323849 : List Nat := [1, 2, 1, 1, 7, 1, 1, 1, 3, 1, 4]
def baseStart_2323849 : Nat := 118140960795 + 2323849 * 2 ^ 59
def prefixEnd_2323849 : Nat := 4983230072969 + 3 ^ 40 * 2323849 * 2
def baseEnd_2323849 : Nat := 1193251505470183663800319

theorem tailTrace_2323849 : CollatzResearch.WordTrace tailWord_2323849 prefixEnd_2323849 1193251505470183663800319 := by
  unfold tailWord_2323849
  simp only [CollatzResearch.WordTrace]
  refine ⟨84757736158099429656934601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56505157438732953104623067 84757736158099429656934601)
  ·
    refine ⟨63568302118574572242700951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84757736158099429656934601 63568302118574572242700951)
    ·
      refine ⟨95352453177861858364051427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63568302118574572242700951 95352453177861858364051427)
      ·
        refine ⟨143028679766792787546077141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95352453177861858364051427 143028679766792787546077141)
        ·
          refine ⟨3352234682034205958111183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 143028679766792787546077141 3352234682034205958111183)
          ·
            refine ⟨5028352023051308937166775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3352234682034205958111183 5028352023051308937166775)
            ·
              refine ⟨7542528034576963405750163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5028352023051308937166775 7542528034576963405750163)
              ·
                refine ⟨11313792051865445108625245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7542528034576963405750163 11313792051865445108625245)
                ·
                  refine ⟨4242672019449541915734467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11313792051865445108625245 4242672019449541915734467)
                  ·
                    refine ⟨6364008029174312873601701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4242672019449541915734467 6364008029174312873601701)
                    ·
                      refine ⟨1193251505470183663800319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6364008029174312873601701 1193251505470183663800319)
                      ·
                        rfl

theorem cell23_2323849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 1, 4].length) (baseStart_2323849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323849 prefixEnd_2323849 := by exact prefixLift 2323849
  have htrace : WordTrace (prefixWord ++ tailWord_2323849) baseStart_2323849 baseEnd_2323849 := by
    simpa [prefixWord, tailWord_2323849, baseEnd_2323849] using wordTrace_append hprefix tailTrace_2323849
  have hstable : (prefixWord ++ tailWord_2323849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323849).length < 2 ^ (prefixWord ++ tailWord_2323849).sum := by decide
  have hdescent : baseEnd_2323849 < baseStart_2323849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323866 : List Nat := [3, 1, 1, 4, 1, 1, 5, 1, 1, 1, 4]
def baseStart_2323866 : Nat := 118140960795 + 2323866 * 2 ^ 59
def prefixEnd_2323866 : Nat := 4983230072969 + 3 ^ 40 * 2323866 * 2
def baseEnd_2323866 : Nat := 1193260234641310097287741

theorem tailTrace_2323866 : CollatzResearch.WordTrace tailWord_2323866 prefixEnd_2323866 1193260234641310097287741 := by
  unfold tailWord_2323866
  simp only [CollatzResearch.WordTrace]
  refine ⟨21189589049759460390075863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56505570799358561040202301 21189589049759460390075863)
  ·
    refine ⟨31784383574639190585113795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21189589049759460390075863 31784383574639190585113795)
    ·
      refine ⟨47676575361958785877670693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31784383574639190585113795 47676575361958785877670693)
      ·
        refine ⟨8939357880367272352063255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47676575361958785877670693 8939357880367272352063255)
        ·
          refine ⟨13409036820550908528094883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8939357880367272352063255 13409036820550908528094883)
          ·
            refine ⟨20113555230826362792142325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13409036820550908528094883 20113555230826362792142325)
            ·
              refine ⟨1885645802889971511763343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20113555230826362792142325 1885645802889971511763343)
              ·
                refine ⟨2828468704334957267645015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1885645802889971511763343 2828468704334957267645015)
                ·
                  refine ⟨4242703056502435901467523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2828468704334957267645015 4242703056502435901467523)
                  ·
                    refine ⟨6364054584753653852201285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4242703056502435901467523 6364054584753653852201285)
                    ·
                      refine ⟨1193260234641310097287741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6364054584753653852201285 1193260234641310097287741)
                      ·
                        rfl

theorem cell23_2323866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_2323866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323866 prefixEnd_2323866 := by exact prefixLift 2323866
  have htrace : WordTrace (prefixWord ++ tailWord_2323866) baseStart_2323866 baseEnd_2323866 := by
    simpa [prefixWord, tailWord_2323866, baseEnd_2323866] using wordTrace_append hprefix tailTrace_2323866
  have hstable : (prefixWord ++ tailWord_2323866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323866).length < 2 ^ (prefixWord ++ tailWord_2323866).sum := by decide
  have hdescent : baseEnd_2323866 < baseStart_2323866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323869 : List Nat := [1, 4, 2, 1, 3, 1, 3, 1, 1, 1, 5]
def baseStart_2323869 : Nat := 118140960795 + 2323869 * 2 ^ 59
def prefixEnd_2323869 : Nat := 4983230072969 + 3 ^ 40 * 2323869 * 2
def baseEnd_2323869 : Nat := 1193261775083273585550227

theorem tailTrace_2323869 : CollatzResearch.WordTrace tailWord_2323869 prefixEnd_2323869 1193261775083273585550227 := by
  unfold tailWord_2323869
  simp only [CollatzResearch.WordTrace]
  refine ⟨84758465618026973072662661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56505643745351315381775107 84758465618026973072662661)
  ·
    refine ⟨15892212303380057451124249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84758465618026973072662661 15892212303380057451124249)
    ·
      refine ⟨11919159227535043088343187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15892212303380057451124249 11919159227535043088343187)
      ·
        refine ⟨17878738841302564632514781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11919159227535043088343187 17878738841302564632514781)
        ·
          refine ⟨6704527065488461737193043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17878738841302564632514781 6704527065488461737193043)
          ·
            refine ⟨10056790598232692605789565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6704527065488461737193043 10056790598232692605789565)
            ·
              refine ⟨3771296474337259727171087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10056790598232692605789565 3771296474337259727171087)
              ·
                refine ⟨5656944711505889590756631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3771296474337259727171087 5656944711505889590756631)
                ·
                  refine ⟨8485417067258834386134947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5656944711505889590756631 8485417067258834386134947)
                  ·
                    refine ⟨12728125600888251579202421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8485417067258834386134947 12728125600888251579202421)
                    ·
                      refine ⟨1193261775083273585550227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12728125600888251579202421 1193261775083273585550227)
                      ·
                        rfl

theorem cell23_2323869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_2323869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323869 prefixEnd_2323869 := by exact prefixLift 2323869
  have htrace : WordTrace (prefixWord ++ tailWord_2323869) baseStart_2323869 baseEnd_2323869 := by
    simpa [prefixWord, tailWord_2323869, baseEnd_2323869] using wordTrace_append hprefix tailTrace_2323869
  have hstable : (prefixWord ++ tailWord_2323869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323869).length < 2 ^ (prefixWord ++ tailWord_2323869).sum := by decide
  have hdescent : baseEnd_2323869 < baseStart_2323869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323902 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 4, 7]
def baseStart_2323902 : Nat := 118140960795 + 2323902 * 2 ^ 59
def prefixEnd_2323902 : Nat := 4983230072969 + 3 ^ 40 * 2323902 * 2
def baseEnd_2323902 : Nat := 397759573314957318812525

theorem tailTrace_2323902 : CollatzResearch.WordTrace tailWord_2323902 prefixEnd_2323902 397759573314957318812525 := by
  unfold tailWord_2323902
  simp only [CollatzResearch.WordTrace]
  refine ⟨10594958653363427463576745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56506446151271613139075973 10594958653363427463576745)
  ·
    refine ⟨7946218990022570597682559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10594958653363427463576745 7946218990022570597682559)
    ·
      refine ⟨11919328485033855896523839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7946218990022570597682559 11919328485033855896523839)
      ·
        refine ⟨17878992727550783844785759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11919328485033855896523839 17878992727550783844785759)
        ·
          refine ⟨26818489091326175767178639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17878992727550783844785759 26818489091326175767178639)
          ·
            refine ⟨40227733636989263650767959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26818489091326175767178639 40227733636989263650767959)
            ·
              refine ⟨60341600455483895476151939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40227733636989263650767959 60341600455483895476151939)
              ·
                refine ⟨90512400683225843214227909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60341600455483895476151939 90512400683225843214227909)
                ·
                  refine ⟨16971075128104845602667733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90512400683225843214227909 16971075128104845602667733)
                  ·
                    refine ⟨397759573314957318812525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16971075128104845602667733 397759573314957318812525)
                    ·
                      rfl

theorem cell23_2323902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_2323902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323902 prefixEnd_2323902 := by exact prefixLift 2323902
  have htrace : WordTrace (prefixWord ++ tailWord_2323902) baseStart_2323902 baseEnd_2323902 := by
    simpa [prefixWord, tailWord_2323902, baseEnd_2323902] using wordTrace_append hprefix tailTrace_2323902
  have hstable : (prefixWord ++ tailWord_2323902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323902).length < 2 ^ (prefixWord ++ tailWord_2323902).sum := by decide
  have hdescent : baseEnd_2323902 < baseStart_2323902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323912 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 2, 2, 5]
def baseStart_2323912 : Nat := 118140960795 + 2323912 * 2 ^ 59
def prefixEnd_2323912 : Nat := 4983230072969 + 3 ^ 40 * 2323912 * 2
def baseEnd_2323912 : Nat := 1193283854751416917312529

theorem tailTrace_2323912 : CollatzResearch.WordTrace tailWord_2323912 prefixEnd_2323912 1193283854751416917312529 := by
  unfold tailWord_2323912
  simp only [CollatzResearch.WordTrace]
  refine ⟨42380016978435595708238995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56506689304580794277651993 42380016978435595708238995)
  ·
    refine ⟨63570025467653393562358493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42380016978435595708238995 63570025467653393562358493)
    ·
      refine ⟨23838759550370022585884435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63570025467653393562358493 23838759550370022585884435)
      ·
        refine ⟨35758139325555033878826653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23838759550370022585884435 35758139325555033878826653)
        ·
          refine ⟨13409302247083137704559995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35758139325555033878826653 13409302247083137704559995)
          ·
            refine ⟨20113953370624706556839993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13409302247083137704559995 20113953370624706556839993)
            ·
              refine ⟨15085465027968529917629995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20113953370624706556839993 15085465027968529917629995)
              ·
                refine ⟨22628197541952794876444993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15085465027968529917629995 22628197541952794876444993)
                ·
                  refine ⟨16971148156464596157333745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22628197541952794876444993 16971148156464596157333745)
                  ·
                    refine ⟨12728361117348447118000309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16971148156464596157333745 12728361117348447118000309)
                    ·
                      refine ⟨1193283854751416917312529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12728361117348447118000309 1193283854751416917312529)
                      ·
                        rfl

theorem cell23_2323912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_2323912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323912 prefixEnd_2323912 := by exact prefixLift 2323912
  have htrace : WordTrace (prefixWord ++ tailWord_2323912) baseStart_2323912 baseEnd_2323912 := by
    simpa [prefixWord, tailWord_2323912, baseEnd_2323912] using wordTrace_append hprefix tailTrace_2323912
  have hstable : (prefixWord ++ tailWord_2323912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323912).length < 2 ^ (prefixWord ++ tailWord_2323912).sum := by decide
  have hdescent : baseEnd_2323912 < baseStart_2323912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323933 : List Nat := [1, 4, 3, 1, 1, 2, 3, 2, 2, 1, 3]
def baseStart_2323933 : Nat := 118140960795 + 2323933 * 2 ^ 59
def prefixEnd_2323933 : Nat := 4983230072969 + 3 ^ 40 * 2323933 * 2
def baseEnd_2323933 : Nat := 1193294637845161335149933

theorem tailTrace_2323933 : CollatzResearch.WordTrace tailWord_2323933 prefixEnd_2323933 1193294637845161335149933 := by
  unfold tailWord_2323933
  simp only [CollatzResearch.WordTrace]
  refine ⟨84760799889795112002992453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56507199926530074668661635 84760799889795112002992453)
  ·
    refine ⟨15892649979336583500561085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84760799889795112002992453 15892649979336583500561085)
    ·
      refine ⟨5959743742251218812710407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15892649979336583500561085 5959743742251218812710407)
      ·
        refine ⟨8939615613376828219065611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5959743742251218812710407 8939615613376828219065611)
        ·
          refine ⟨13409423420065242328598417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8939615613376828219065611 13409423420065242328598417)
          ·
            refine ⟨10057067565048931746448813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13409423420065242328598417 10057067565048931746448813)
            ·
              refine ⟨3771400336893349404918305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10057067565048931746448813 3771400336893349404918305)
              ·
                refine ⟨2828550252670012053688729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3771400336893349404918305 2828550252670012053688729)
                ·
                  refine ⟨2121412689502509040266547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2828550252670012053688729 2121412689502509040266547)
                  ·
                    refine ⟨3182119034253763560399821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2121412689502509040266547 3182119034253763560399821)
                    ·
                      refine ⟨1193294637845161335149933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3182119034253763560399821 1193294637845161335149933)
                      ·
                        rfl

theorem cell23_2323933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_2323933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323933 prefixEnd_2323933 := by exact prefixLift 2323933
  have htrace : WordTrace (prefixWord ++ tailWord_2323933) baseStart_2323933 baseEnd_2323933 := by
    simpa [prefixWord, tailWord_2323933, baseEnd_2323933] using wordTrace_append hprefix tailTrace_2323933
  have hstable : (prefixWord ++ tailWord_2323933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323933).length < 2 ^ (prefixWord ++ tailWord_2323933).sum := by decide
  have hdescent : baseEnd_2323933 < baseStart_2323933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2323962 : List Nat := [3, 1, 1, 1, 1, 2, 3, 4, 7]
def baseStart_2323962 : Nat := 118140960795 + 2323962 * 2 ^ 59
def prefixEnd_2323962 : Nat := 4983230072969 + 3 ^ 40 * 2323962 * 2
def baseEnd_2323962 : Nat := 132589947642682413520811

theorem tailTrace_2323962 : CollatzResearch.WordTrace tailWord_2323962 prefixEnd_2323962 132589947642682413520811 := by
  unfold tailWord_2323962
  simp only [CollatzResearch.WordTrace]
  refine ⟨21190464401672512488949535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56507905071126699970532093 21190464401672512488949535)
  ·
    refine ⟨31785696602508768733424303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21190464401672512488949535 31785696602508768733424303)
    ·
      refine ⟨47678544903763153100136455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31785696602508768733424303 47678544903763153100136455)
      ·
        refine ⟨71517817355644729650204683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47678544903763153100136455 71517817355644729650204683)
        ·
          refine ⟨107276726033467094475307025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71517817355644729650204683 107276726033467094475307025)
          ·
            refine ⟨80457544525100320856480269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107276726033467094475307025 80457544525100320856480269)
            ·
              refine ⟨30171579196912620321180101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80457544525100320856480269 30171579196912620321180101)
              ·
                refine ⟨5657171099421116310221269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30171579196912620321180101 5657171099421116310221269)
                ·
                  refine ⟨132589947642682413520811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5657171099421116310221269 132589947642682413520811)
                  ·
                    rfl

theorem cell23_2323962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 7].length) (baseStart_2323962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2323962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2323962 prefixEnd_2323962 := by exact prefixLift 2323962
  have htrace : WordTrace (prefixWord ++ tailWord_2323962) baseStart_2323962 baseEnd_2323962 := by
    simpa [prefixWord, tailWord_2323962, baseEnd_2323962] using wordTrace_append hprefix tailTrace_2323962
  have hstable : (prefixWord ++ tailWord_2323962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2323962).length < 2 ^ (prefixWord ++ tailWord_2323962).sum := by decide
  have hdescent : baseEnd_2323962 < baseStart_2323962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2323962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324046 : List Nat := [4, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2]
def baseStart_2324046 : Nat := 118140960795 + 2324046 * 2 ^ 59
def prefixEnd_2324046 : Nat := 4983230072969 + 3 ^ 40 * 2324046 * 2
def baseEnd_2324046 : Nat := 1193352661159119393036913

theorem tailTrace_2324046 : CollatzResearch.WordTrace tailWord_2324046 prefixEnd_2324046 1193352661159119393036913 := by
  unfold tailWord_2324046
  simp only [CollatzResearch.WordTrace]
  refine ⟨10595615167298216537731999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56509947558923821534570661 10595615167298216537731999)
  ·
    refine ⟨15893422750947324806597999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10595615167298216537731999 15893422750947324806597999)
    ·
      refine ⟨23840134126420987209896999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15893422750947324806597999 23840134126420987209896999)
      ·
        refine ⟨35760201189631480814845499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23840134126420987209896999 35760201189631480814845499)
        ·
          refine ⟨53640301784447221222268249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35760201189631480814845499 53640301784447221222268249)
          ·
            refine ⟨40230226338335415916701187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53640301784447221222268249 40230226338335415916701187)
            ·
              refine ⟨60345339507503123875051781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40230226338335415916701187 60345339507503123875051781)
              ·
                refine ⟨11314751157656835726572209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60345339507503123875051781 11314751157656835726572209)
                ·
                  refine ⟨8486063368242626794929157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11314751157656835726572209 8486063368242626794929157)
                  ·
                    refine ⟨1591136881545492524049217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8486063368242626794929157 1591136881545492524049217)
                    ·
                      refine ⟨1193352661159119393036913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1591136881545492524049217 1193352661159119393036913)
                      ·
                        rfl

theorem cell23_2324046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2].length) (baseStart_2324046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324046 prefixEnd_2324046 := by exact prefixLift 2324046
  have htrace : WordTrace (prefixWord ++ tailWord_2324046) baseStart_2324046 baseEnd_2324046 := by
    simpa [prefixWord, tailWord_2324046, baseEnd_2324046] using wordTrace_append hprefix tailTrace_2324046
  have hstable : (prefixWord ++ tailWord_2324046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324046).length < 2 ^ (prefixWord ++ tailWord_2324046).sum := by decide
  have hdescent : baseEnd_2324046 < baseStart_2324046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324096 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 5, 1, 3]
def baseStart_2324096 : Nat := 118140960795 + 2324096 * 2 ^ 59
def prefixEnd_2324096 : Nat := 4983230072969 + 3 ^ 40 * 2324096 * 2
def baseEnd_2324096 : Nat := 1193378335191844197411683

theorem tailTrace_2324096 : CollatzResearch.WordTrace tailWord_2324096 prefixEnd_2324096 1193378335191844197411683 := by
  unfold tailWord_2324096
  simp only [CollatzResearch.WordTrace]
  refine ⟨42383372494102295420588071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56511163325469727227450761 42383372494102295420588071)
  ·
    refine ⟨63575058741153443130882107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42383372494102295420588071 63575058741153443130882107)
    ·
      refine ⟨95362588111730164696323161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63575058741153443130882107 95362588111730164696323161)
      ·
        refine ⟨71521941083797623522242371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95362588111730164696323161 71521941083797623522242371)
        ·
          refine ⟨107282911625696435283363557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71521941083797623522242371 107282911625696435283363557)
          ·
            refine ⟨20115545929818081615630667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107282911625696435283363557 20115545929818081615630667)
            ·
              refine ⟨30173318894727122423446001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20115545929818081615630667 30173318894727122423446001)
              ·
                refine ⟨22629989171045341817584501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30173318894727122423446001 22629989171045341817584501)
                ·
                  refine ⟨2121561484785500795398547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22629989171045341817584501 2121561484785500795398547)
                  ·
                    refine ⟨3182342227178251193097821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2121561484785500795398547 3182342227178251193097821)
                    ·
                      refine ⟨1193378335191844197411683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3182342227178251193097821 1193378335191844197411683)
                      ·
                        rfl

theorem cell23_2324096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 5, 1, 3].length) (baseStart_2324096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324096 prefixEnd_2324096 := by exact prefixLift 2324096
  have htrace : WordTrace (prefixWord ++ tailWord_2324096) baseStart_2324096 baseEnd_2324096 := by
    simpa [prefixWord, tailWord_2324096, baseEnd_2324096] using wordTrace_append hprefix tailTrace_2324096
  have hstable : (prefixWord ++ tailWord_2324096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324096).length < 2 ^ (prefixWord ++ tailWord_2324096).sum := by decide
  have hdescent : baseEnd_2324096 < baseStart_2324096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324146 : List Nat := [3, 2, 1, 1, 1, 2, 3, 2, 4, 4]
def baseStart_2324146 : Nat := 118140960795 + 2324146 * 2 ^ 59
def prefixEnd_2324146 : Nat := 4983230072969 + 3 ^ 40 * 2324146 * 2
def baseEnd_2324146 : Nat := 397801336408189667262151

theorem tailTrace_2324146 : CollatzResearch.WordTrace tailWord_2324146 prefixEnd_2324146 397801336408189667262151 := by
  unfold tailWord_2324146
  simp only [CollatzResearch.WordTrace]
  refine ⟨21192142159505862345124073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56512379092015632920330861 21192142159505862345124073)
  ·
    refine ⟨15894106619629396758843055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21192142159505862345124073 15894106619629396758843055)
    ·
      refine ⟨23841159929444095138264583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15894106619629396758843055 23841159929444095138264583)
      ·
        refine ⟨35761739894166142707396875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23841159929444095138264583 35761739894166142707396875)
        ·
          refine ⟨53642609841249214061095313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35761739894166142707396875 53642609841249214061095313)
          ·
            refine ⟨40231957380936910545821485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53642609841249214061095313 40231957380936910545821485)
            ·
              refine ⟨15086984017851341454683057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40231957380936910545821485 15086984017851341454683057)
              ·
                refine ⟨11315238013388506091012293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15086984017851341454683057 11315238013388506091012293)
                ·
                  refine ⟨2121607127510344892064805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11315238013388506091012293 2121607127510344892064805)
                  ·
                    refine ⟨397801336408189667262151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2121607127510344892064805 397801336408189667262151)
                    ·
                      rfl

theorem cell23_2324146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_2324146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324146 prefixEnd_2324146 := by exact prefixLift 2324146
  have htrace : WordTrace (prefixWord ++ tailWord_2324146) baseStart_2324146 baseEnd_2324146 := by
    simpa [prefixWord, tailWord_2324146, baseEnd_2324146] using wordTrace_append hprefix tailTrace_2324146
  have hstable : (prefixWord ++ tailWord_2324146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324146).length < 2 ^ (prefixWord ++ tailWord_2324146).sum := by decide
  have hdescent : baseEnd_2324146 < baseStart_2324146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324150 : List Nat := [5, 1, 3, 1, 1, 1, 2, 3, 1, 5]
def baseStart_2324150 : Nat := 118140960795 + 2324150 * 2 ^ 59
def prefixEnd_2324150 : Nat := 4983230072969 + 3 ^ 40 * 2324150 * 2
def baseEnd_2324150 : Nat := 397802021049062328712145

theorem tailTrace_2324150 : CollatzResearch.WordTrace tailWord_2324150 prefixEnd_2324150 397802021049062328712145 := by
  unfold tailWord_2324150
  simp only [CollatzResearch.WordTrace]
  refine ⟨5298044658125559878977619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56512476353339305375761269 5298044658125559878977619)
  ·
    refine ⟨7947066987188339818466429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5298044658125559878977619 7947066987188339818466429)
    ·
      refine ⟨2980150120195627431924911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7947066987188339818466429 2980150120195627431924911)
      ·
        refine ⟨4470225180293441147887367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2980150120195627431924911 4470225180293441147887367)
        ·
          refine ⟨6705337770440161721831051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4470225180293441147887367 6705337770440161721831051)
          ·
            refine ⟨10058006655660242582746577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6705337770440161721831051 10058006655660242582746577)
            ·
              refine ⟨7543504991745181937059933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10058006655660242582746577 7543504991745181937059933)
              ·
                refine ⟨2828814371904443226397475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7543504991745181937059933 2828814371904443226397475)
                ·
                  refine ⟨4243221557856664839596213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2828814371904443226397475 4243221557856664839596213)
                  ·
                    refine ⟨397802021049062328712145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4243221557856664839596213 397802021049062328712145)
                    ·
                      rfl

theorem cell23_2324150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_2324150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324150 prefixEnd_2324150 := by exact prefixLift 2324150
  have htrace : WordTrace (prefixWord ++ tailWord_2324150) baseStart_2324150 baseEnd_2324150 := by
    simpa [prefixWord, tailWord_2324150, baseEnd_2324150] using wordTrace_append hprefix tailTrace_2324150
  have hstable : (prefixWord ++ tailWord_2324150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324150).length < 2 ^ (prefixWord ++ tailWord_2324150).sum := by decide
  have hdescent : baseEnd_2324150 < baseStart_2324150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324153 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 5, 2, 2]
def baseStart_2324153 : Nat := 118140960795 + 2324153 * 2 ^ 59
def prefixEnd_2324153 : Nat := 4983230072969 + 3 ^ 40 * 2324153 * 2
def baseEnd_2324153 : Nat := 1193407603589150474398921

theorem tailTrace_2324153 : CollatzResearch.WordTrace tailWord_2324153 prefixEnd_2324153 1193407603589150474398921 := by
  unfold tailWord_2324153
  simp only [CollatzResearch.WordTrace]
  refine ⟨84768823948998089576001113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56512549299332059717334075 84768823948998089576001113)
  ·
    refine ⟨63576617961748567182000835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84768823948998089576001113 63576617961748567182000835)
    ·
      refine ⟨95364926942622850773001253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63576617961748567182000835 95364926942622850773001253)
      ·
        refine ⟨17880923801741784519937735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95364926942622850773001253 17880923801741784519937735)
        ·
          refine ⟨26821385702612676779906603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17880923801741784519937735 26821385702612676779906603)
          ·
            refine ⟨40232078553919015169859905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26821385702612676779906603 40232078553919015169859905)
            ·
              refine ⟨30174058915439261377394929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40232078553919015169859905 30174058915439261377394929)
              ·
                refine ⟨22630544186579446033046197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30174058915439261377394929 22630544186579446033046197)
                ·
                  refine ⟨2121613517491823065598081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22630544186579446033046197 2121613517491823065598081)
                  ·
                    refine ⟨1591210138118867299198561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2121613517491823065598081 1591210138118867299198561)
                    ·
                      refine ⟨1193407603589150474398921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1591210138118867299198561 1193407603589150474398921)
                      ·
                        rfl

theorem cell23_2324153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_2324153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324153 prefixEnd_2324153 := by exact prefixLift 2324153
  have htrace : WordTrace (prefixWord ++ tailWord_2324153) baseStart_2324153 baseEnd_2324153 := by
    simpa [prefixWord, tailWord_2324153, baseEnd_2324153] using wordTrace_append hprefix tailTrace_2324153
  have hstable : (prefixWord ++ tailWord_2324153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324153).length < 2 ^ (prefixWord ++ tailWord_2324153).sum := by decide
  have hdescent : baseEnd_2324153 < baseStart_2324153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324156 : List Nat := [2, 2, 2, 3, 1, 2, 1, 3, 1, 1, 5]
def baseStart_2324156 : Nat := 118140960795 + 2324156 * 2 ^ 59
def prefixEnd_2324156 : Nat := 4983230072969 + 3 ^ 40 * 2324156 * 2
def baseEnd_2324156 : Nat := 1193409144031113962661407

theorem tailTrace_2324156 : CollatzResearch.WordTrace tailWord_2324156 prefixEnd_2324156 1193409144031113962661407 := by
  unfold tailWord_2324156
  simp only [CollatzResearch.WordTrace]
  refine ⟨42384466683993610544180161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56512622245324814058906881 42384466683993610544180161)
  ·
    refine ⟨31788350012995207908135121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42384466683993610544180161 31788350012995207908135121)
    ·
      refine ⟨23841262509746405931101341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31788350012995207908135121 23841262509746405931101341)
      ·
        refine ⟨8940473441154902224163003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23841262509746405931101341 8940473441154902224163003)
        ·
          refine ⟨13410710161732353336244505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8940473441154902224163003 13410710161732353336244505)
          ·
            refine ⟨10058032621299265002183379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13410710161732353336244505 10058032621299265002183379)
            ·
              refine ⟨15087048931948897503275069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10058032621299265002183379 15087048931948897503275069)
              ·
                refine ⟨5657643349480836563728151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15087048931948897503275069 5657643349480836563728151)
                ·
                  refine ⟨8486465024221254845592227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5657643349480836563728151 8486465024221254845592227)
                  ·
                    refine ⟨12729697536331882268388341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8486465024221254845592227 12729697536331882268388341)
                    ·
                      refine ⟨1193409144031113962661407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12729697536331882268388341 1193409144031113962661407)
                      ·
                        rfl

theorem cell23_2324156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_2324156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324156 prefixEnd_2324156 := by exact prefixLift 2324156
  have htrace : WordTrace (prefixWord ++ tailWord_2324156) baseStart_2324156 baseEnd_2324156 := by
    simpa [prefixWord, tailWord_2324156, baseEnd_2324156] using wordTrace_append hprefix tailTrace_2324156
  have hstable : (prefixWord ++ tailWord_2324156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324156).length < 2 ^ (prefixWord ++ tailWord_2324156).sum := by decide
  have hdescent : baseEnd_2324156 < baseStart_2324156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324180 : List Nat := [2, 4, 1, 3, 1, 2, 1, 3, 2, 4]
def baseStart_2324180 : Nat := 118140960795 + 2324180 * 2 ^ 59
def prefixEnd_2324180 : Nat := 4983230072969 + 3 ^ 40 * 2324180 * 2
def baseEnd_2324180 : Nat := 397807155855607289587099

theorem tailTrace_2324180 : CollatzResearch.WordTrace tailWord_2324180 prefixEnd_2324180 397807155855607289587099 := by
  unfold tailWord_2324180
  simp only [CollatzResearch.WordTrace]
  refine ⟨42384904359950136593616997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56513205813266848791489329 42384904359950136593616997)
  ·
    refine ⟨7947169567490650611303187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42384904359950136593616997 7947169567490650611303187)
    ·
      refine ⟨11920754351235975916954781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7947169567490650611303187 11920754351235975916954781)
      ·
        refine ⟨4470282881713490968858043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11920754351235975916954781 4470282881713490968858043)
        ·
          refine ⟨6705424322570236453287065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4470282881713490968858043 6705424322570236453287065)
          ·
            refine ⟨5029068241927677339965299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6705424322570236453287065 5029068241927677339965299)
            ·
              refine ⟨7543602362891516009947949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5029068241927677339965299 7543602362891516009947949)
              ·
                refine ⟨2828850886084318503730481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7543602362891516009947949 2828850886084318503730481)
                ·
                  refine ⟨2121638164563238877797861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2828850886084318503730481 2121638164563238877797861)
                  ·
                    refine ⟨397807155855607289587099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2121638164563238877797861 397807155855607289587099)
                    ·
                      rfl

theorem cell23_2324180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_2324180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324180 prefixEnd_2324180 := by exact prefixLift 2324180
  have htrace : WordTrace (prefixWord ++ tailWord_2324180) baseStart_2324180 baseEnd_2324180 := by
    simpa [prefixWord, tailWord_2324180, baseEnd_2324180] using wordTrace_append hprefix tailTrace_2324180
  have hstable : (prefixWord ++ tailWord_2324180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324180).length < 2 ^ (prefixWord ++ tailWord_2324180).sum := by decide
  have hdescent : baseEnd_2324180 < baseStart_2324180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324220 : List Nat := [2, 2, 2, 1, 3, 1, 4, 2, 2, 1, 3]
def baseStart_2324220 : Nat := 118140960795 + 2324220 * 2 ^ 59
def prefixEnd_2324220 : Nat := 4983230072969 + 3 ^ 40 * 2324220 * 2
def baseEnd_2324220 : Nat := 1193442006793001712261113

theorem tailTrace_2324220 : CollatzResearch.WordTrace tailWord_2324220 prefixEnd_2324220 1193442006793001712261113 := by
  unfold tailWord_2324220
  simp only [CollatzResearch.WordTrace]
  refine ⟨42385633819877680009345057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56514178426503573345793409 42385633819877680009345057)
  ·
    refine ⟨31789225364908260007008793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42385633819877680009345057 31789225364908260007008793)
    ·
      refine ⟨23841919023681195005256595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31789225364908260007008793 23841919023681195005256595)
      ·
        refine ⟨35762878535521792507884893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23841919023681195005256595 35762878535521792507884893)
        ·
          refine ⟨13411079450820672190456835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35762878535521792507884893 13411079450820672190456835)
          ·
            refine ⟨20116619176231008285685253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13411079450820672190456835 20116619176231008285685253)
            ·
              refine ⟨3771866095543314053565985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20116619176231008285685253 3771866095543314053565985)
              ·
                refine ⟨2828899571657485540174489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3771866095543314053565985 2828899571657485540174489)
                ·
                  refine ⟨2121674678743114155130867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2828899571657485540174489 2121674678743114155130867)
                  ·
                    refine ⟨3182512018114671232696301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2121674678743114155130867 3182512018114671232696301)
                    ·
                      refine ⟨1193442006793001712261113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3182512018114671232696301 1193442006793001712261113)
                      ·
                        rfl

theorem cell23_2324220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 2, 1, 3].length) (baseStart_2324220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324220 prefixEnd_2324220 := by exact prefixLift 2324220
  have htrace : WordTrace (prefixWord ++ tailWord_2324220) baseStart_2324220 baseEnd_2324220 := by
    simpa [prefixWord, tailWord_2324220, baseEnd_2324220] using wordTrace_append hprefix tailTrace_2324220
  have hstable : (prefixWord ++ tailWord_2324220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324220).length < 2 ^ (prefixWord ++ tailWord_2324220).sum := by decide
  have hdescent : baseEnd_2324220 < baseStart_2324220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324256 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 4]
def baseStart_2324256 : Nat := 118140960795 + 2324256 * 2 ^ 59
def prefixEnd_2324256 : Nat := 4983230072969 + 3 ^ 40 * 2324256 * 2
def baseEnd_2324256 : Nat := 1193460492096563571410947

theorem tailTrace_2324256 : CollatzResearch.WordTrace tailWord_2324256 prefixEnd_2324256 1193460492096563571410947 := by
  unfold tailWord_2324256
  simp only [CollatzResearch.WordTrace]
  refine ⟨42386290333812469083500311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56515053778416625444667081 42386290333812469083500311)
  ·
    refine ⟨63579435500718703625250467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42386290333812469083500311 63579435500718703625250467)
    ·
      refine ⟨95369153251078055437875701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63579435500718703625250467 95369153251078055437875701)
      ·
        refine ⟨8940858117288567697300847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95369153251078055437875701 8940858117288567697300847)
        ·
          refine ⟨13411287175932851545951271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8940858117288567697300847 13411287175932851545951271)
          ·
            refine ⟨20116930763899277318926907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13411287175932851545951271 20116930763899277318926907)
            ·
              refine ⟨30175396145848915978390361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20116930763899277318926907 30175396145848915978390361)
              ·
                refine ⟨22631547109386686983792771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30175396145848915978390361 22631547109386686983792771)
                ·
                  refine ⟨33947320664080030475689157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22631547109386686983792771 33947320664080030475689157)
                  ·
                    refine ⟨6365122624515005714191717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33947320664080030475689157 6365122624515005714191717)
                    ·
                      refine ⟨1193460492096563571410947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6365122624515005714191717 1193460492096563571410947)
                      ·
                        rfl

theorem cell23_2324256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_2324256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324256 prefixEnd_2324256 := by exact prefixLift 2324256
  have htrace : WordTrace (prefixWord ++ tailWord_2324256) baseStart_2324256 baseEnd_2324256 := by
    simpa [prefixWord, tailWord_2324256, baseEnd_2324256] using wordTrace_append hprefix tailTrace_2324256
  have hstable : (prefixWord ++ tailWord_2324256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324256).length < 2 ^ (prefixWord ++ tailWord_2324256).sum := by decide
  have hdescent : baseEnd_2324256 < baseStart_2324256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324260 : List Nat := [2, 3, 1, 3, 2, 1, 2, 2, 1, 4, 2]
def baseStart_2324260 : Nat := 118140960795 + 2324260 * 2 ^ 59
def prefixEnd_2324260 : Nat := 4983230072969 + 3 ^ 40 * 2324260 * 2
def baseEnd_2324260 : Nat := 1193462546019181555760929

theorem tailTrace_2324260 : CollatzResearch.WordTrace tailWord_2324260 prefixEnd_2324260 1193462546019181555760929 := by
  unfold tailWord_2324260
  simp only [CollatzResearch.WordTrace]
  refine ⟨42386363279805223425073117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56515151039740297900097489 42386363279805223425073117)
  ·
    refine ⟨15894886229926958784402419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42386363279805223425073117 15894886229926958784402419)
    ·
      refine ⟨23842329344890438176603629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15894886229926958784402419 23842329344890438176603629)
      ·
        refine ⟨8940873504333914316226361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23842329344890438176603629 8940873504333914316226361)
        ·
          refine ⟨6705655128250435737169771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8940873504333914316226361 6705655128250435737169771)
          ·
            refine ⟨10058482692375653605754657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6705655128250435737169771 10058482692375653605754657)
            ·
              refine ⟨7543862019281740204315993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10058482692375653605754657 7543862019281740204315993)
              ·
                refine ⟨5657896514461305153236995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7543862019281740204315993 5657896514461305153236995)
                ·
                  refine ⟨8486844771691957729855493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5657896514461305153236995 8486844771691957729855493)
                  ·
                    refine ⟨1591283394692242074347905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8486844771691957729855493 1591283394692242074347905)
                    ·
                      refine ⟨1193462546019181555760929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1591283394692242074347905 1193462546019181555760929)
                      ·
                        rfl

theorem cell23_2324260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_2324260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324260 prefixEnd_2324260 := by exact prefixLift 2324260
  have htrace : WordTrace (prefixWord ++ tailWord_2324260) baseStart_2324260 baseEnd_2324260 := by
    simpa [prefixWord, tailWord_2324260, baseEnd_2324260] using wordTrace_append hprefix tailTrace_2324260
  have hstable : (prefixWord ++ tailWord_2324260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324260).length < 2 ^ (prefixWord ++ tailWord_2324260).sum := by decide
  have hdescent : baseEnd_2324260 < baseStart_2324260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324264 : List Nat := [2, 1, 5, 1, 1, 4, 2, 1, 1, 3, 2]
def baseStart_2324264 : Nat := 118140960795 + 2324264 * 2 ^ 59
def prefixEnd_2324264 : Nat := 4983230072969 + 3 ^ 40 * 2324264 * 2
def baseEnd_2324264 : Nat := 1193464599941799540110911

theorem tailTrace_2324264 : CollatzResearch.WordTrace tailWord_2324264 prefixEnd_2324264 1193464599941799540110911 := by
  unfold tailWord_2324264
  simp only [CollatzResearch.WordTrace]
  refine ⟨42386436225797977766645923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56515248301063970355527897 42386436225797977766645923)
  ·
    refine ⟨63579654338696966649968885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42386436225797977766645923 63579654338696966649968885)
    ·
      refine ⟨5960592594252840623434583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63579654338696966649968885 5960592594252840623434583)
      ·
        refine ⟨8940888891379260935151875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5960592594252840623434583 8940888891379260935151875)
        ·
          refine ⟨13411333337068891402727813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8940888891379260935151875 13411333337068891402727813)
          ·
            refine ⟨2514625000700417138011465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13411333337068891402727813 2514625000700417138011465)
            ·
              refine ⟨1885968750525312853508599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2514625000700417138011465 1885968750525312853508599)
              ·
                refine ⟨2828953125787969280262899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1885968750525312853508599 2828953125787969280262899)
                ·
                  refine ⟨4243429688681953920394349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2828953125787969280262899 4243429688681953920394349)
                  ·
                    refine ⟨1591286133255732720147881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4243429688681953920394349 1591286133255732720147881)
                    ·
                      refine ⟨1193464599941799540110911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1591286133255732720147881 1193464599941799540110911)
                      ·
                        rfl

theorem cell23_2324264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_2324264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324264 prefixEnd_2324264 := by exact prefixLift 2324264
  have htrace : WordTrace (prefixWord ++ tailWord_2324264) baseStart_2324264 baseEnd_2324264 := by
    simpa [prefixWord, tailWord_2324264, baseEnd_2324264] using wordTrace_append hprefix tailTrace_2324264
  have hstable : (prefixWord ++ tailWord_2324264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324264).length < 2 ^ (prefixWord ++ tailWord_2324264).sum := by decide
  have hdescent : baseEnd_2324264 < baseStart_2324264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324277 : List Nat := [1, 3, 3, 1, 4, 1, 1, 1, 4, 2, 2]
def baseStart_2324277 : Nat := 118140960795 + 2324277 * 2 ^ 59
def prefixEnd_2324277 : Nat := 4983230072969 + 3 ^ 40 * 2324277 * 2
def baseEnd_2324277 : Nat := 1193471275190307989248351

theorem tailTrace_2324277 : CollatzResearch.WordTrace tailWord_2324277 prefixEnd_2324277 1193471275190307989248351 := by
  unfold tailWord_2324277
  simp only [CollatzResearch.WordTrace]
  refine ⟨84773346600548858753515085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56515564400365905835676723 84773346600548858753515085)
  ·
    refine ⟨31790004975205822032568157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84773346600548858753515085 31790004975205822032568157)
    ·
      refine ⟨11921251865702183262213059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31790004975205822032568157 11921251865702183262213059)
      ·
        refine ⟨17881877798553274893319589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11921251865702183262213059 17881877798553274893319589)
        ·
          refine ⟨3352852087228739042497423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17881877798553274893319589 3352852087228739042497423)
          ·
            refine ⟨5029278130843108563746135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3352852087228739042497423 5029278130843108563746135)
            ·
              refine ⟨7543917196264662845619203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5029278130843108563746135 7543917196264662845619203)
              ·
                refine ⟨11315875794396994268428805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7543917196264662845619203 11315875794396994268428805)
                ·
                  refine ⟨2121726711449436425330401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11315875794396994268428805 2121726711449436425330401)
                  ·
                    refine ⟨1591295033587077318997801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2121726711449436425330401 1591295033587077318997801)
                    ·
                      refine ⟨1193471275190307989248351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1591295033587077318997801 1193471275190307989248351)
                      ·
                        rfl

theorem cell23_2324277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_2324277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324277 prefixEnd_2324277 := by exact prefixLift 2324277
  have htrace : WordTrace (prefixWord ++ tailWord_2324277) baseStart_2324277 baseEnd_2324277 := by
    simpa [prefixWord, tailWord_2324277, baseEnd_2324277] using wordTrace_append hprefix tailTrace_2324277
  have hstable : (prefixWord ++ tailWord_2324277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324277).length < 2 ^ (prefixWord ++ tailWord_2324277).sum := by decide
  have hdescent : baseEnd_2324277 < baseStart_2324277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324294 : List Nat := [6, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2]
def baseStart_2324294 : Nat := 118140960795 + 2324294 * 2 ^ 59
def prefixEnd_2324294 : Nat := 4983230072969 + 3 ^ 40 * 2324294 * 2
def baseEnd_2324294 : Nat := 1193480004361434422735773

theorem tailTrace_2324294 : CollatzResearch.WordTrace tailWord_2324294 prefixEnd_2324294 1193480004361434422735773 := by
  unfold tailWord_2324294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2649186457546477208027623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 56515977760991513771255957 2649186457546477208027623)
  ·
    refine ⟨3973779686319715812041435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2649186457546477208027623 3973779686319715812041435)
    ·
      refine ⟨5960669529479573718062153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3973779686319715812041435 5960669529479573718062153)
      ·
        refine ⟨4470502147109680288546615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5960669529479573718062153 4470502147109680288546615)
        ·
          refine ⟨6705753220664520432819923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4470502147109680288546615 6705753220664520432819923)
          ·
            refine ⟨10058629830996780649229885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6705753220664520432819923 10058629830996780649229885)
            ·
              refine ⟨3771986186623792743461207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10058629830996780649229885 3771986186623792743461207)
              ·
                refine ⟨5657979279935689115191811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3771986186623792743461207 5657979279935689115191811)
                ·
                  refine ⟨8486968919903533672787717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5657979279935689115191811 8486968919903533672787717)
                  ·
                    refine ⟨1591306672481912563647697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8486968919903533672787717 1591306672481912563647697)
                    ·
                      refine ⟨1193480004361434422735773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1591306672481912563647697 1193480004361434422735773)
                      ·
                        rfl

theorem cell23_2324294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_2324294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324294 prefixEnd_2324294 := by exact prefixLift 2324294
  have htrace : WordTrace (prefixWord ++ tailWord_2324294) baseStart_2324294 baseEnd_2324294 := by
    simpa [prefixWord, tailWord_2324294, baseEnd_2324294] using wordTrace_append hprefix tailTrace_2324294
  have hstable : (prefixWord ++ tailWord_2324294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324294).length < 2 ^ (prefixWord ++ tailWord_2324294).sum := by decide
  have hdescent : baseEnd_2324294 < baseStart_2324294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324296 : List Nat := [2, 1, 3, 1, 1, 4, 1, 2, 1, 7]
def baseStart_2324296 : Nat := 118140960795 + 2324296 * 2 ^ 59
def prefixEnd_2324296 : Nat := 4983230072969 + 3 ^ 40 * 2324296 * 2
def baseEnd_2324296 : Nat := 397827010440914471636921

theorem tailTrace_2324296 : CollatzResearch.WordTrace tailWord_2324296 prefixEnd_2324296 397827010440914471636921 := by
  unfold tailWord_2324296
  simp only [CollatzResearch.WordTrace]
  refine ⟨42387019793740012499228371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56516026391653349998971161 42387019793740012499228371)
  ·
    refine ⟨63580529690610018748842557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42387019793740012499228371 63580529690610018748842557)
    ·
      refine ⟨23842698633978757030815959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63580529690610018748842557 23842698633978757030815959)
      ·
        refine ⟨35764047950968135546223939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23842698633978757030815959 35764047950968135546223939)
        ·
          refine ⟨53646071926452203319335909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35764047950968135546223939 53646071926452203319335909)
          ·
            refine ⟨10058638486209788122375483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53646071926452203319335909 10058638486209788122375483)
            ·
              refine ⟨15087957729314682183563225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10058638486209788122375483 15087957729314682183563225)
              ·
                refine ⟨11315968296986011637672419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15087957729314682183563225 11315968296986011637672419)
                ·
                  refine ⟨16973952445479017456508629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11315968296986011637672419 16973952445479017456508629)
                  ·
                    refine ⟨397827010440914471636921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16973952445479017456508629 397827010440914471636921)
                    ·
                      rfl

theorem cell23_2324296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_2324296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324296 prefixEnd_2324296 := by exact prefixLift 2324296
  have htrace : WordTrace (prefixWord ++ tailWord_2324296) baseStart_2324296 baseEnd_2324296 := by
    simpa [prefixWord, tailWord_2324296, baseEnd_2324296] using wordTrace_append hprefix tailTrace_2324296
  have hstable : (prefixWord ++ tailWord_2324296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324296).length < 2 ^ (prefixWord ++ tailWord_2324296).sum := by decide
  have hdescent : baseEnd_2324296 < baseStart_2324296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324333 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 4, 1, 4]
def baseStart_2324333 : Nat := 118140960795 + 2324333 * 2 ^ 59
def prefixEnd_2324333 : Nat := 4983230072969 + 3 ^ 40 * 2324333 * 2
def baseEnd_2324333 : Nat := 1193500030106959770148093

theorem tailTrace_2324333 : CollatzResearch.WordTrace tailWord_2324333 prefixEnd_2324333 1193500030106959770148093 := by
  unfold tailWord_2324333
  simp only [CollatzResearch.WordTrace]
  refine ⟨84775389088345980317553653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56516926058897320211702435 84775389088345980317553653)
  ·
    refine ⟨7947692727032435654770655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84775389088345980317553653 7947692727032435654770655)
    ·
      refine ⟨11921539090548653482155983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7947692727032435654770655 11921539090548653482155983)
      ·
        refine ⟨17882308635822980223233975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11921539090548653482155983 17882308635822980223233975)
        ·
          refine ⟨26823462953734470334850963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17882308635822980223233975 26823462953734470334850963)
          ·
            refine ⟨40235194430601705502276445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26823462953734470334850963 40235194430601705502276445)
            ·
              refine ⟨15088197911475639563353667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40235194430601705502276445 15088197911475639563353667)
              ·
                refine ⟨22632296867213459345030501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15088197911475639563353667 22632296867213459345030501)
                ·
                  refine ⟨4243555662602523627193219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22632296867213459345030501 4243555662602523627193219)
                  ·
                    refine ⟨6365333493903785440789829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4243555662602523627193219 6365333493903785440789829)
                    ·
                      refine ⟨1193500030106959770148093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6365333493903785440789829 1193500030106959770148093)
                      ·
                        rfl

theorem cell23_2324333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_2324333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324333 prefixEnd_2324333 := by exact prefixLift 2324333
  have htrace : WordTrace (prefixWord ++ tailWord_2324333) baseStart_2324333 baseEnd_2324333 := by
    simpa [prefixWord, tailWord_2324333, baseEnd_2324333] using wordTrace_append hprefix tailTrace_2324333
  have hstable : (prefixWord ++ tailWord_2324333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324333).length < 2 ^ (prefixWord ++ tailWord_2324333).sum := by decide
  have hdescent : baseEnd_2324333 < baseStart_2324333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324346 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 2, 1, 6]
def baseStart_2324346 : Nat := 118140960795 + 2324346 * 2 ^ 59
def prefixEnd_2324346 : Nat := 4983230072969 + 3 ^ 40 * 2324346 * 2
def baseEnd_2324346 : Nat := 1193506705355468219285533

theorem tailTrace_2324346 : CollatzResearch.WordTrace tailWord_2324346 prefixEnd_2324346 1193506705355468219285533 := by
  unfold tailWord_2324346
  simp only [CollatzResearch.WordTrace]
  refine ⟨21193965809324720884444223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56517242158199255691851261 21193965809324720884444223)
  ·
    refine ⟨31790948713987081326666335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21193965809324720884444223 31790948713987081326666335)
    ·
      refine ⟨47686423070980621989999503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31790948713987081326666335 47686423070980621989999503)
      ·
        refine ⟨71529634606470932984999255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47686423070980621989999503 71529634606470932984999255)
        ·
          refine ⟨107294451909706399477498883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71529634606470932984999255 107294451909706399477498883)
          ·
            refine ⟨160941677864559599216248325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107294451909706399477498883 160941677864559599216248325)
            ·
              refine ⟨30176564599604924853046561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 160941677864559599216248325 30176564599604924853046561)
              ·
                refine ⟨22632423449703693639784921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30176564599604924853046561 22632423449703693639784921)
                ·
                  refine ⟨16974317587277770229838691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22632423449703693639784921 16974317587277770229838691)
                  ·
                    refine ⟨25461476380916655344758037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16974317587277770229838691 25461476380916655344758037)
                    ·
                      refine ⟨1193506705355468219285533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25461476380916655344758037 1193506705355468219285533)
                      ·
                        rfl

theorem cell23_2324346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_2324346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324346 prefixEnd_2324346 := by exact prefixLift 2324346
  have htrace : WordTrace (prefixWord ++ tailWord_2324346) baseStart_2324346 baseEnd_2324346 := by
    simpa [prefixWord, tailWord_2324346, baseEnd_2324346] using wordTrace_append hprefix tailTrace_2324346
  have hstable : (prefixWord ++ tailWord_2324346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324346).length < 2 ^ (prefixWord ++ tailWord_2324346).sum := by decide
  have hdescent : baseEnd_2324346 < baseStart_2324346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324396 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 7]
def baseStart_2324396 : Nat := 118140960795 + 2324396 * 2 ^ 59
def prefixEnd_2324396 : Nat := 4983230072969 + 3 ^ 40 * 2324396 * 2
def baseEnd_2324396 : Nat := 1193532379388193023660303

theorem tailTrace_2324396 : CollatzResearch.WordTrace tailWord_2324396 prefixEnd_2324396 1193532379388193023660303 := by
  unfold tailWord_2324396
  simp only [CollatzResearch.WordTrace]
  refine ⟨42388843443558871038548521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56518457924745161384731361 42388843443558871038548521)
  ·
    refine ⟨31791632582669153278911391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42388843443558871038548521 31791632582669153278911391)
    ·
      refine ⟨47687448874003729918367087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31791632582669153278911391 47687448874003729918367087)
      ·
        refine ⟨71531173311005594877550631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47687448874003729918367087 71531173311005594877550631)
        ·
          refine ⟨107296759966508392316325947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71531173311005594877550631 107296759966508392316325947)
          ·
            refine ⟨160945139949762588474488921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107296759966508392316325947 160945139949762588474488921)
            ·
              refine ⟨120708854962321941355866691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160945139949762588474488921 120708854962321941355866691)
              ·
                refine ⟨181063282443482912033800037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120708854962321941355866691 181063282443482912033800037)
                ·
                  refine ⟨33949365458153046006337507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 181063282443482912033800037 33949365458153046006337507)
                  ·
                    refine ⟨50924048187229569009506261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33949365458153046006337507 50924048187229569009506261)
                    ·
                      refine ⟨1193532379388193023660303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 50924048187229569009506261 1193532379388193023660303)
                      ·
                        rfl

theorem cell23_2324396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_2324396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324396 prefixEnd_2324396 := by exact prefixLift 2324396
  have htrace : WordTrace (prefixWord ++ tailWord_2324396) baseStart_2324396 baseEnd_2324396 := by
    simpa [prefixWord, tailWord_2324396, baseEnd_2324396] using wordTrace_append hprefix tailTrace_2324396
  have hstable : (prefixWord ++ tailWord_2324396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324396).length < 2 ^ (prefixWord ++ tailWord_2324396).sum := by decide
  have hdescent : baseEnd_2324396 < baseStart_2324396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324437 : List Nat := [1, 3, 2, 3, 2, 1, 4, 1, 1, 5]
def baseStart_2324437 : Nat := 118140960795 + 2324437 * 2 ^ 59
def prefixEnd_2324437 : Nat := 4983230072969 + 3 ^ 40 * 2324437 * 2
def baseEnd_2324437 : Nat := 397851144031675787749205

theorem tailTrace_2324437 : CollatzResearch.WordTrace tailWord_2324437 prefixEnd_2324437 397851144031675787749205 := by
  unfold tailWord_2324437
  simp only [CollatzResearch.WordTrace]
  refine ⟨84779182279969206079339565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56519454853312804052893043 84779182279969206079339565)
  ·
    refine ⟨31792193354988452279752337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84779182279969206079339565 31792193354988452279752337)
    ·
      refine ⟨23844145016241339209814253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31792193354988452279752337 23844145016241339209814253)
      ·
        refine ⟨8941554381090502203680345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23844145016241339209814253 8941554381090502203680345)
        ·
          refine ⟨6706165785817876652760259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8941554381090502203680345 6706165785817876652760259)
          ·
            refine ⟨10059248678726814979140389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6706165785817876652760259 10059248678726814979140389)
            ·
              refine ⟨1886109127261277808588823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10059248678726814979140389 1886109127261277808588823)
              ·
                refine ⟨2829163690891916712883235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1886109127261277808588823 2829163690891916712883235)
                ·
                  refine ⟨4243745536337875069324853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2829163690891916712883235 4243745536337875069324853)
                  ·
                    refine ⟨397851144031675787749205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4243745536337875069324853 397851144031675787749205)
                    ·
                      rfl

theorem cell23_2324437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 1, 5].length) (baseStart_2324437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324437 prefixEnd_2324437 := by exact prefixLift 2324437
  have htrace : WordTrace (prefixWord ++ tailWord_2324437) baseStart_2324437 baseEnd_2324437 := by
    simpa [prefixWord, tailWord_2324437, baseEnd_2324437] using wordTrace_append hprefix tailTrace_2324437
  have hstable : (prefixWord ++ tailWord_2324437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324437).length < 2 ^ (prefixWord ++ tailWord_2324437).sum := by decide
  have hdescent : baseEnd_2324437 < baseStart_2324437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324440 : List Nat := [2, 1, 2, 2, 2, 2, 3, 3, 1, 1, 4]
def baseStart_2324440 : Nat := 118140960795 + 2324440 * 2 ^ 59
def prefixEnd_2324440 : Nat := 4983230072969 + 3 ^ 40 * 2324440 * 2
def baseEnd_2324440 : Nat := 1193554972536990851510101

theorem tailTrace_2324440 : CollatzResearch.WordTrace tailWord_2324440 prefixEnd_2324440 1193554972536990851510101 := by
  unfold tailWord_2324440
  simp only [CollatzResearch.WordTrace]
  refine ⟨42389645849479168795849387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56519527799305558394465849 42389645849479168795849387)
  ·
    refine ⟨63584468774218753193774081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42389645849479168795849387 63584468774218753193774081)
    ·
      refine ⟨47688351580664064895330561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63584468774218753193774081 47688351580664064895330561)
      ·
        refine ⟨35766263685498048671497921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47688351580664064895330561 35766263685498048671497921)
        ·
          refine ⟨26824697764123536503623441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35766263685498048671497921 26824697764123536503623441)
          ·
            refine ⟨20118523323092652377717581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26824697764123536503623441 20118523323092652377717581)
            ·
              refine ⟨7544446246159744641644093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20118523323092652377717581 7544446246159744641644093)
              ·
                refine ⟨2829167342309904240616535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7544446246159744641644093 2829167342309904240616535)
                ·
                  refine ⟨4243751013464856360924803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2829167342309904240616535 4243751013464856360924803)
                  ·
                    refine ⟨6365626520197284541387205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4243751013464856360924803 6365626520197284541387205)
                    ·
                      refine ⟨1193554972536990851510101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6365626520197284541387205 1193554972536990851510101)
                      ·
                        rfl

theorem cell23_2324440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_2324440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324440 prefixEnd_2324440 := by exact prefixLift 2324440
  have htrace : WordTrace (prefixWord ++ tailWord_2324440) baseStart_2324440 baseEnd_2324440 := by
    simpa [prefixWord, tailWord_2324440, baseEnd_2324440] using wordTrace_append hprefix tailTrace_2324440
  have hstable : (prefixWord ++ tailWord_2324440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324440).length < 2 ^ (prefixWord ++ tailWord_2324440).sum := by decide
  have hdescent : baseEnd_2324440 < baseStart_2324440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324508 : List Nat := [2, 2, 3, 1, 3, 2, 3, 2, 1, 2, 2]
def baseStart_2324508 : Nat := 118140960795 + 2324508 * 2 ^ 59
def prefixEnd_2324508 : Nat := 4983230072969 + 3 ^ 40 * 2324508 * 2
def baseEnd_2324508 : Nat := 1193589889221496585459789

theorem tailTrace_2324508 : CollatzResearch.WordTrace tailWord_2324508 prefixEnd_2324508 1193589889221496585459789 := by
  unfold tailWord_2324508
  simp only [CollatzResearch.WordTrace]
  refine ⟨42390885931355992602587089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56521181241807990136782785 42390885931355992602587089)
  ·
    refine ⟨31793164448516994451940317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42390885931355992602587089 31793164448516994451940317)
    ·
      refine ⟨11922436668193872919477619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31793164448516994451940317 11922436668193872919477619)
      ·
        refine ⟨17883655002290809379216429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11922436668193872919477619 17883655002290809379216429)
        ·
          refine ⟨6706370625859053517206161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17883655002290809379216429 6706370625859053517206161)
          ·
            refine ⟨5029777969394290137904621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6706370625859053517206161 5029777969394290137904621)
            ·
              refine ⟨1886166738522858801714233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5029777969394290137904621 1886166738522858801714233)
              ·
                refine ⟨1414625053892144101285675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1886166738522858801714233 1414625053892144101285675)
                ·
                  refine ⟨2121937580838216151928513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1414625053892144101285675 2121937580838216151928513)
                  ·
                    refine ⟨1591453185628662113946385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2121937580838216151928513 1591453185628662113946385)
                    ·
                      refine ⟨1193589889221496585459789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1591453185628662113946385 1193589889221496585459789)
                      ·
                        rfl

theorem cell23_2324508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_2324508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324508 prefixEnd_2324508 := by exact prefixLift 2324508
  have htrace : WordTrace (prefixWord ++ tailWord_2324508) baseStart_2324508 baseEnd_2324508 := by
    simpa [prefixWord, tailWord_2324508, baseEnd_2324508] using wordTrace_append hprefix tailTrace_2324508
  have hstable : (prefixWord ++ tailWord_2324508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324508).length < 2 ^ (prefixWord ++ tailWord_2324508).sum := by decide
  have hdescent : baseEnd_2324508 < baseStart_2324508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324534 : List Nat := [5, 1, 2, 1, 1, 1, 3, 1, 3, 3, 2]
def baseStart_2324534 : Nat := 118140960795 + 2324534 * 2 ^ 59
def prefixEnd_2324534 : Nat := 4983230072969 + 3 ^ 40 * 2324534 * 2
def baseEnd_2324534 : Nat := 1193603239718513483734669

theorem tailTrace_2324534 : CollatzResearch.WordTrace tailWord_2324534 prefixEnd_2324534 1193603239718513483734669 := by
  unfold tailWord_2324534
  simp only [CollatzResearch.WordTrace]
  refine ⟨5298920010038611977851291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56521813440411861097080437 5298920010038611977851291)
  ·
    refine ⟨7948380015057917966776937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5298920010038611977851291 7948380015057917966776937)
    ·
      refine ⟨5961285011293438475082703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7948380015057917966776937 5961285011293438475082703)
      ·
        refine ⟨8941927516940157712624055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5961285011293438475082703 8941927516940157712624055)
        ·
          refine ⟨13412891275410236568936083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8941927516940157712624055 13412891275410236568936083)
          ·
            refine ⟨20119336913115354853404125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13412891275410236568936083 20119336913115354853404125)
            ·
              refine ⟨7544751342418258070026547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20119336913115354853404125 7544751342418258070026547)
              ·
                refine ⟨11317127013627387105039821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7544751342418258070026547 11317127013627387105039821)
                ·
                  refine ⟨4243922630110270164389933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11317127013627387105039821 4243922630110270164389933)
                  ·
                    refine ⟨1591470986291351311646225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4243922630110270164389933 1591470986291351311646225)
                    ·
                      refine ⟨1193603239718513483734669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1591470986291351311646225 1193603239718513483734669)
                      ·
                        rfl

theorem cell23_2324534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_2324534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324534 prefixEnd_2324534 := by exact prefixLift 2324534
  have htrace : WordTrace (prefixWord ++ tailWord_2324534) baseStart_2324534 baseEnd_2324534 := by
    simpa [prefixWord, tailWord_2324534, baseEnd_2324534] using wordTrace_append hprefix tailTrace_2324534
  have hstable : (prefixWord ++ tailWord_2324534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324534).length < 2 ^ (prefixWord ++ tailWord_2324534).sum := by decide
  have hdescent : baseEnd_2324534 < baseStart_2324534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324547 : List Nat := [1, 1, 1, 3, 1, 2, 2, 4, 4, 2, 2]
def baseStart_2324547 : Nat := 118140960795 + 2324547 * 2 ^ 59
def prefixEnd_2324547 : Nat := 4983230072969 + 3 ^ 40 * 2324547 * 2
def baseEnd_2324547 : Nat := 1193609914967021932872109

theorem tailTrace_2324547 : CollatzResearch.WordTrace tailWord_2324547 prefixEnd_2324547 1193609914967021932872109 := by
  unfold tailWord_2324547
  simp only [CollatzResearch.WordTrace]
  refine ⟨84783194309570694865843895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56522129539713796577229263 84783194309570694865843895)
  ·
    refine ⟨127174791464356042298765843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84783194309570694865843895 127174791464356042298765843)
    ·
      refine ⟨190762187196534063448148765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127174791464356042298765843 190762187196534063448148765)
      ·
        refine ⟨71535820198700273793055787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190762187196534063448148765 71535820198700273793055787)
        ·
          refine ⟨107303730298050410689583681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71535820198700273793055787 107303730298050410689583681)
          ·
            refine ⟨80477797723537808017187761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107303730298050410689583681 80477797723537808017187761)
            ·
              refine ⟨60358348292653356012890821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80477797723537808017187761 60358348292653356012890821)
              ·
                refine ⟨11317190304872504252417029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60358348292653356012890821 11317190304872504252417029)
                ·
                  refine ⟨2121973182163594547328193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11317190304872504252417029 2121973182163594547328193)
                  ·
                    refine ⟨1591479886622695910496145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2121973182163594547328193 1591479886622695910496145)
                    ·
                      refine ⟨1193609914967021932872109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1591479886622695910496145 1193609914967021932872109)
                      ·
                        rfl

theorem cell23_2324547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 4, 2, 2].length) (baseStart_2324547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324547 prefixEnd_2324547 := by exact prefixLift 2324547
  have htrace : WordTrace (prefixWord ++ tailWord_2324547) baseStart_2324547 baseEnd_2324547 := by
    simpa [prefixWord, tailWord_2324547, baseEnd_2324547] using wordTrace_append hprefix tailTrace_2324547
  have hstable : (prefixWord ++ tailWord_2324547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324547).length < 2 ^ (prefixWord ++ tailWord_2324547).sum := by decide
  have hdescent : baseEnd_2324547 < baseStart_2324547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324580 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 1, 5, 3]
def baseStart_2324580 : Nat := 118140960795 + 2324580 * 2 ^ 59
def prefixEnd_2324580 : Nat := 4983230072969 + 3 ^ 40 * 2324580 * 2
def baseEnd_2324580 : Nat := 1193626859828620303759457

theorem tailTrace_2324580 : CollatzResearch.WordTrace tailWord_2324580 prefixEnd_2324580 1193626859828620303759457 := by
  unfold tailWord_2324580
  simp only [CollatzResearch.WordTrace]
  refine ⟨42392198959225570750897597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56522931945634094334530129 42392198959225570750897597)
  ·
    refine ⟨15897074609709589031586599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42392198959225570750897597 15897074609709589031586599)
    ·
      refine ⟨23845611914564383547379899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15897074609709589031586599 23845611914564383547379899)
      ·
        refine ⟨35768417871846575321069849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23845611914564383547379899 35768417871846575321069849)
        ·
          refine ⟨26826313403884931490802387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35768417871846575321069849 26826313403884931490802387)
          ·
            refine ⟨40239470105827397236203581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26826313403884931490802387 40239470105827397236203581)
            ·
              refine ⟨15089801289685273963576343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40239470105827397236203581 15089801289685273963576343)
              ·
                refine ⟨22634701934527910945364515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15089801289685273963576343 22634701934527910945364515)
                ·
                  refine ⟨33952052901791866418046773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22634701934527910945364515 33952052901791866418046773)
                  ·
                    refine ⟨3183004959542987476691885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33952052901791866418046773 3183004959542987476691885)
                    ·
                      refine ⟨1193626859828620303759457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3183004959542987476691885 1193626859828620303759457)
                      ·
                        rfl

theorem cell23_2324580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_2324580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324580 prefixEnd_2324580 := by exact prefixLift 2324580
  have htrace : WordTrace (prefixWord ++ tailWord_2324580) baseStart_2324580 baseEnd_2324580 := by
    simpa [prefixWord, tailWord_2324580, baseEnd_2324580] using wordTrace_append hprefix tailTrace_2324580
  have hstable : (prefixWord ++ tailWord_2324580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324580).length < 2 ^ (prefixWord ++ tailWord_2324580).sum := by decide
  have hdescent : baseEnd_2324580 < baseStart_2324580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324623 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 11]
def baseStart_2324623 : Nat := 118140960795 + 2324623 * 2 ^ 59
def prefixEnd_2324623 : Nat := 4983230072969 + 3 ^ 40 * 2324623 * 2
def baseEnd_2324623 : Nat := 1193648939496763635521759

theorem tailTrace_2324623 : CollatzResearch.WordTrace tailWord_2324623 prefixEnd_2324623 1193648939496763635521759 := by
  unfold tailWord_2324623
  simp only [CollatzResearch.WordTrace]
  refine ⟨84785966257295359845610523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56523977504863573230407015 84785966257295359845610523)
  ·
    refine ⟨127178949385943039768415785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84785966257295359845610523 127178949385943039768415785)
    ·
      refine ⟨95384212039457279826311839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127178949385943039768415785 95384212039457279826311839)
      ·
        refine ⟨143076318059185919739467759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95384212039457279826311839 143076318059185919739467759)
        ·
          refine ⟨214614477088778879609201639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143076318059185919739467759 214614477088778879609201639)
          ·
            refine ⟨321921715633168319413802459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214614477088778879609201639 321921715633168319413802459)
            ·
              refine ⟨482882573449752479120703689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321921715633168319413802459 482882573449752479120703689)
              ·
                refine ⟨362161930087314359340527767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 482882573449752479120703689 362161930087314359340527767)
                ·
                  refine ⟨543242895130971539010791651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 362161930087314359340527767 543242895130971539010791651)
                  ·
                    refine ⟨814864342696457308516187477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 543242895130971539010791651 814864342696457308516187477)
                    ·
                      refine ⟨1193648939496763635521759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 814864342696457308516187477 1193648939496763635521759)
                      ·
                        rfl

theorem cell23_2324623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 11].length) (baseStart_2324623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324623 prefixEnd_2324623 := by exact prefixLift 2324623
  have htrace : WordTrace (prefixWord ++ tailWord_2324623) baseStart_2324623 baseEnd_2324623 := by
    simpa [prefixWord, tailWord_2324623, baseEnd_2324623] using wordTrace_append hprefix tailTrace_2324623
  have hstable : (prefixWord ++ tailWord_2324623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324623).length < 2 ^ (prefixWord ++ tailWord_2324623).sum := by decide
  have hdescent : baseEnd_2324623 < baseStart_2324623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324697 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 3, 5, 2]
def baseStart_2324697 : Nat := 118140960795 + 2324697 * 2 ^ 59
def prefixEnd_2324697 : Nat := 4983230072969 + 3 ^ 40 * 2324697 * 2
def baseEnd_2324697 : Nat := 1193686937065196345996419

theorem tailTrace_2324697 : CollatzResearch.WordTrace tailWord_2324697 prefixEnd_2324697 1193686937065196345996419 := by
  unfold tailWord_2324697
  simp only [CollatzResearch.WordTrace]
  refine ⟨84788665259027270483804345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56525776839351513655869563 84788665259027270483804345)
  ·
    refine ⟨63591498944270452862853259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84788665259027270483804345 63591498944270452862853259)
    ·
      refine ⟨95387248416405679294279889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63591498944270452862853259 95387248416405679294279889)
      ·
        refine ⟨71540436312304259470709917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95387248416405679294279889 71540436312304259470709917)
        ·
          refine ⟨26827663617114097301516219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71540436312304259470709917 26827663617114097301516219)
          ·
            refine ⟨40241495425671145952274329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26827663617114097301516219 40241495425671145952274329)
            ·
              refine ⟨30181121569253359464205747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40241495425671145952274329 30181121569253359464205747)
              ·
                refine ⟨45271682353880039196308621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30181121569253359464205747 45271682353880039196308621)
                ·
                  refine ⟨16976880882705014698615733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45271682353880039196308621 16976880882705014698615733)
                  ·
                    refine ⟨1591582582753595127995225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16976880882705014698615733 1591582582753595127995225)
                    ·
                      refine ⟨1193686937065196345996419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1591582582753595127995225 1193686937065196345996419)
                      ·
                        rfl

theorem cell23_2324697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 5, 2].length) (baseStart_2324697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324697 prefixEnd_2324697 := by exact prefixLift 2324697
  have htrace : WordTrace (prefixWord ++ tailWord_2324697) baseStart_2324697 baseEnd_2324697 := by
    simpa [prefixWord, tailWord_2324697, baseEnd_2324697] using wordTrace_append hprefix tailTrace_2324697
  have hstable : (prefixWord ++ tailWord_2324697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324697).length < 2 ^ (prefixWord ++ tailWord_2324697).sum := by decide
  have hdescent : baseEnd_2324697 < baseStart_2324697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324747 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 5, 2, 3]
def baseStart_2324747 : Nat := 118140960795 + 2324747 * 2 ^ 59
def prefixEnd_2324747 : Nat := 4983230072969 + 3 ^ 40 * 2324747 * 2
def baseEnd_2324747 : Nat := 1193712611097921150371189

theorem tailTrace_2324747 : CollatzResearch.WordTrace tailWord_2324747 prefixEnd_2324747 1193712611097921150371189 := by
  unfold tailWord_2324747
  simp only [CollatzResearch.WordTrace]
  refine ⟨84790488908846129023124495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56526992605897419348749663 84790488908846129023124495)
  ·
    refine ⟨127185733363269193534686743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84790488908846129023124495 127185733363269193534686743)
    ·
      refine ⟨190778600044903790302030115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127185733363269193534686743 190778600044903790302030115)
      ·
        refine ⟨286167900067355685453045173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190778600044903790302030115 286167900067355685453045173)
        ·
          refine ⟨26828240631314595511222985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 286167900067355685453045173 26828240631314595511222985)
          ·
            refine ⟨20121180473485946633417239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26828240631314595511222985 20121180473485946633417239)
            ·
              refine ⟨30181770710228919950125859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20121180473485946633417239 30181770710228919950125859)
              ·
                refine ⟨45272656065343379925188789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30181770710228919950125859 45272656065343379925188789)
                ·
                  refine ⟨4244311506125941867986449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45272656065343379925188789 4244311506125941867986449)
                  ·
                    refine ⟨3183233629594456400989837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4244311506125941867986449 3183233629594456400989837)
                    ·
                      refine ⟨1193712611097921150371189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3183233629594456400989837 1193712611097921150371189)
                      ·
                        rfl

theorem cell23_2324747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 2, 3].length) (baseStart_2324747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324747 prefixEnd_2324747 := by exact prefixLift 2324747
  have htrace : WordTrace (prefixWord ++ tailWord_2324747) baseStart_2324747 baseEnd_2324747 := by
    simpa [prefixWord, tailWord_2324747, baseEnd_2324747] using wordTrace_append hprefix tailTrace_2324747
  have hstable : (prefixWord ++ tailWord_2324747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324747).length < 2 ^ (prefixWord ++ tailWord_2324747).sum := by decide
  have hdescent : baseEnd_2324747 < baseStart_2324747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324757 : List Nat := [1, 3, 2, 1, 2, 1, 3, 3, 1, 2, 4]
def baseStart_2324757 : Nat := 118140960795 + 2324757 * 2 ^ 59
def prefixEnd_2324757 : Nat := 4983230072969 + 3 ^ 40 * 2324757 * 2
def baseEnd_2324757 : Nat := 1193717745904466111246143

theorem tailTrace_2324757 : CollatzResearch.WordTrace tailWord_2324757 prefixEnd_2324757 1193717745904466111246143 := by
  unfold tailWord_2324757
  simp only [CollatzResearch.WordTrace]
  refine ⟨84790853638809900730988525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56527235759206600487325683 84790853638809900730988525)
  ·
    refine ⟨31796570114553712774120697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84790853638809900730988525 31796570114553712774120697)
    ·
      refine ⟨23847427585915284580590523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31796570114553712774120697 23847427585915284580590523)
      ·
        refine ⟨35771141378872926870885785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23847427585915284580590523 35771141378872926870885785)
        ·
          refine ⟨26828356034154695153164339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35771141378872926870885785 26828356034154695153164339)
          ·
            refine ⟨40242534051232042729746509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26828356034154695153164339 40242534051232042729746509)
            ·
              refine ⟨15090950269212016023654941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40242534051232042729746509 15090950269212016023654941)
              ·
                refine ⟨5659106350954506008870603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15090950269212016023654941 5659106350954506008870603)
                ·
                  refine ⟨8488659526431759013305905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5659106350954506008870603 8488659526431759013305905)
                  ·
                    refine ⟨6366494644823819259979429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8488659526431759013305905 6366494644823819259979429)
                    ·
                      refine ⟨1193717745904466111246143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6366494644823819259979429 1193717745904466111246143)
                      ·
                        rfl

theorem cell23_2324757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_2324757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324757 prefixEnd_2324757 := by exact prefixLift 2324757
  have htrace : WordTrace (prefixWord ++ tailWord_2324757) baseStart_2324757 baseEnd_2324757 := by
    simpa [prefixWord, tailWord_2324757, baseEnd_2324757] using wordTrace_append hprefix tailTrace_2324757
  have hstable : (prefixWord ++ tailWord_2324757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324757).length < 2 ^ (prefixWord ++ tailWord_2324757).sum := by decide
  have hdescent : baseEnd_2324757 < baseStart_2324757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324764 : List Nat := [2, 2, 3, 1, 1, 1, 1, 6, 1, 2, 3]
def baseStart_2324764 : Nat := 118140960795 + 2324764 * 2 ^ 59
def prefixEnd_2324764 : Nat := 4983230072969 + 3 ^ 40 * 2324764 * 2
def baseEnd_2324764 : Nat := 1193721340269047583858611

theorem tailTrace_2324764 : CollatzResearch.WordTrace tailWord_2324764 prefixEnd_2324764 1193721340269047583858611 := by
  unfold tailWord_2324764
  simp only [CollatzResearch.WordTrace]
  refine ⟨42395554474892270463246673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56527405966523027284328897 42395554474892270463246673)
  ·
    refine ⟨31796665856169202847435005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42395554474892270463246673 31796665856169202847435005)
    ·
      refine ⟨11923749696063451067788127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31796665856169202847435005 11923749696063451067788127)
      ·
        refine ⟨17885624544095176601682191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11923749696063451067788127 17885624544095176601682191)
        ·
          refine ⟨26828436816142764902523287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17885624544095176601682191 26828436816142764902523287)
          ·
            refine ⟨40242655224214147353784931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26828436816142764902523287 40242655224214147353784931)
            ·
              refine ⟨60363982836321221030677397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40242655224214147353784931 60363982836321221030677397)
              ·
                refine ⟨2829561695452557235813003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60363982836321221030677397 2829561695452557235813003)
                ·
                  refine ⟨4244342543178835853719505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2829561695452557235813003 4244342543178835853719505)
                  ·
                    refine ⟨3183256907384126890289629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4244342543178835853719505 3183256907384126890289629)
                    ·
                      refine ⟨1193721340269047583858611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3183256907384126890289629 1193721340269047583858611)
                      ·
                        rfl

theorem cell23_2324764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_2324764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324764 prefixEnd_2324764 := by exact prefixLift 2324764
  have htrace : WordTrace (prefixWord ++ tailWord_2324764) baseStart_2324764 baseEnd_2324764 := by
    simpa [prefixWord, tailWord_2324764, baseEnd_2324764] using wordTrace_append hprefix tailTrace_2324764
  have hstable : (prefixWord ++ tailWord_2324764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324764).length < 2 ^ (prefixWord ++ tailWord_2324764).sum := by decide
  have hdescent : baseEnd_2324764 < baseStart_2324764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324765 : List Nat := [1, 4, 2, 3, 3, 1, 1, 1, 2, 3, 2]
def baseStart_2324765 : Nat := 118140960795 + 2324765 * 2 ^ 59
def prefixEnd_2324765 : Nat := 4983230072969 + 3 ^ 40 * 2324765 * 2
def baseEnd_2324765 : Nat := 1193721853749702079946107

theorem tailTrace_2324765 : CollatzResearch.WordTrace tailWord_2324765 prefixEnd_2324765 1193721853749702079946107 := by
  unfold tailWord_2324765
  simp only [CollatzResearch.WordTrace]
  refine ⟨84791145422780918097279749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56527430281853945398186499 84791145422780918097279749)
  ·
    refine ⟨15898339766771422143239953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84791145422780918097279749 15898339766771422143239953)
    ·
      refine ⟨11923754825078566607429965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15898339766771422143239953 11923754825078566607429965)
      ·
        refine ⟨4471408059404462477786237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11923754825078566607429965 4471408059404462477786237)
        ·
          refine ⟨1676778022276673429169839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4471408059404462477786237 1676778022276673429169839)
          ·
            refine ⟨2515167033415010143754759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1676778022276673429169839 2515167033415010143754759)
            ·
              refine ⟨3772750550122515215632139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2515167033415010143754759 3772750550122515215632139)
              ·
                refine ⟨5659125825183772823448209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3772750550122515215632139 5659125825183772823448209)
                ·
                  refine ⟨4244344368887829617586157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5659125825183772823448209 4244344368887829617586157)
                  ·
                    refine ⟨1591629138332936106594809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4244344368887829617586157 1591629138332936106594809)
                    ·
                      refine ⟨1193721853749702079946107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1591629138332936106594809 1193721853749702079946107)
                      ·
                        rfl

theorem cell23_2324765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_2324765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324765 prefixEnd_2324765 := by exact prefixLift 2324765
  have htrace : WordTrace (prefixWord ++ tailWord_2324765) baseStart_2324765 baseEnd_2324765 := by
    simpa [prefixWord, tailWord_2324765, baseEnd_2324765] using wordTrace_append hprefix tailTrace_2324765
  have hstable : (prefixWord ++ tailWord_2324765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324765).length < 2 ^ (prefixWord ++ tailWord_2324765).sum := by decide
  have hdescent : baseEnd_2324765 < baseStart_2324765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324788 : List Nat := [2, 5, 1, 1, 1, 4, 1, 2, 2, 4]
def baseStart_2324788 : Nat := 118140960795 + 2324788 * 2 ^ 59
def prefixEnd_2324788 : Nat := 4983230072969 + 3 ^ 40 * 2324788 * 2
def baseEnd_2324788 : Nat := 397911221268251829986167

theorem tailTrace_2324788 : CollatzResearch.WordTrace tailWord_2324788 prefixEnd_2324788 397911221268251829986167 := by
  unfold tailWord_2324788
  simp only [CollatzResearch.WordTrace]
  refine ⟨42395992150848796512683509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56527989534465062016911345 42395992150848796512683509)
  ·
    refine ⟨3974624264142074673064079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42395992150848796512683509 3974624264142074673064079)
    ·
      refine ⟨5961936396213112009596119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3974624264142074673064079 5961936396213112009596119)
      ·
        refine ⟨8942904594319668014394179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5961936396213112009596119 8942904594319668014394179)
        ·
          refine ⟨13414356891479502021591269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8942904594319668014394179 13414356891479502021591269)
          ·
            refine ⟨2515191917152406629048363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13414356891479502021591269 2515191917152406629048363)
            ·
              refine ⟨3772787875728609943572545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2515191917152406629048363 3772787875728609943572545)
              ·
                refine ⟨2829590906796457457679409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3772787875728609943572545 2829590906796457457679409)
                ·
                  refine ⟨2122193180097343093259557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2829590906796457457679409 2122193180097343093259557)
                  ·
                    refine ⟨397911221268251829986167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2122193180097343093259557 397911221268251829986167)
                    ·
                      rfl

theorem cell23_2324788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_2324788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324788 prefixEnd_2324788 := by exact prefixLift 2324788
  have htrace : WordTrace (prefixWord ++ tailWord_2324788) baseStart_2324788 baseEnd_2324788 := by
    simpa [prefixWord, tailWord_2324788, baseEnd_2324788] using wordTrace_append hprefix tailTrace_2324788
  have hstable : (prefixWord ++ tailWord_2324788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324788).length < 2 ^ (prefixWord ++ tailWord_2324788).sum := by decide
  have hdescent : baseEnd_2324788 < baseStart_2324788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324837 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 1, 3, 5]
def baseStart_2324837 : Nat := 118140960795 + 2324837 * 2 ^ 59
def prefixEnd_2324837 : Nat := 4983230072969 + 3 ^ 40 * 2324837 * 2
def baseEnd_2324837 : Nat := 1193758824356825798245775

theorem tailTrace_2324837 : CollatzResearch.WordTrace tailWord_2324837 prefixEnd_2324837 1193758824356825798245775 := by
  unfold tailWord_2324837
  simp only [CollatzResearch.WordTrace]
  refine ⟨84793771478520074393900765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56529180985680049595933843 84793771478520074393900765)
  ·
    refine ⟨31797664304445027897712787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84793771478520074393900765 31797664304445027897712787)
    ·
      refine ⟨47696496456667541846569181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31797664304445027897712787 47696496456667541846569181)
      ·
        refine ⟨17886186171250328192463443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47696496456667541846569181 17886186171250328192463443)
        ·
          refine ⟨26829279256875492288695165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17886186171250328192463443 26829279256875492288695165)
          ·
            refine ⟨10060979721328309608260687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26829279256875492288695165 10060979721328309608260687)
            ·
              refine ⟨15091469581992464412391031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10060979721328309608260687 15091469581992464412391031)
              ·
                refine ⟨22637204372988696618586547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15091469581992464412391031 22637204372988696618586547)
                ·
                  refine ⟨33955806559483044927879821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22637204372988696618586547 33955806559483044927879821)
                  ·
                    refine ⟨12733427459806141847954933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33955806559483044927879821 12733427459806141847954933)
                    ·
                      refine ⟨1193758824356825798245775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12733427459806141847954933 1193758824356825798245775)
                      ·
                        rfl

theorem cell23_2324837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_2324837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324837 prefixEnd_2324837 := by exact prefixLift 2324837
  have htrace : WordTrace (prefixWord ++ tailWord_2324837) baseStart_2324837 baseEnd_2324837 := by
    simpa [prefixWord, tailWord_2324837, baseEnd_2324837] using wordTrace_append hprefix tailTrace_2324837
  have hstable : (prefixWord ++ tailWord_2324837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324837).length < 2 ^ (prefixWord ++ tailWord_2324837).sum := by decide
  have hdescent : baseEnd_2324837 < baseStart_2324837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324847 : List Nat := [1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 4]
def baseStart_2324847 : Nat := 118140960795 + 2324847 * 2 ^ 59
def prefixEnd_2324847 : Nat := 4983230072969 + 3 ^ 40 * 2324847 * 2
def baseEnd_2324847 : Nat := 1193763959163370759120729

theorem tailTrace_2324847 : CollatzResearch.WordTrace tailWord_2324847 prefixEnd_2324847 1193763959163370759120729 := by
  unfold tailWord_2324847
  simp only [CollatzResearch.WordTrace]
  refine ⟨84794136208483846101764795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56529424138989230734509863 84794136208483846101764795)
  ·
    refine ⟨127191204312725769152647193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84794136208483846101764795 127191204312725769152647193)
    ·
      refine ⟨95393403234544326864485395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127191204312725769152647193 95393403234544326864485395)
      ·
        refine ⟨143090104851816490296728093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95393403234544326864485395 143090104851816490296728093)
        ·
          refine ⟨53658789319431183861273035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143090104851816490296728093 53658789319431183861273035)
          ·
            refine ⟨80488183979146775791909553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53658789319431183861273035 80488183979146775791909553)
            ·
              refine ⟨60366137984360081843932165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80488183979146775791909553 60366137984360081843932165)
              ·
                refine ⟨11318650872067515345737281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60366137984360081843932165 11318650872067515345737281)
                ·
                  refine ⟨8488988154050636509302961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11318650872067515345737281 8488988154050636509302961)
                  ·
                    refine ⟨6366741115537977381977221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8488988154050636509302961 6366741115537977381977221)
                    ·
                      refine ⟨1193763959163370759120729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6366741115537977381977221 1193763959163370759120729)
                      ·
                        rfl

theorem cell23_2324847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 4].length) (baseStart_2324847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324847 prefixEnd_2324847 := by exact prefixLift 2324847
  have htrace : WordTrace (prefixWord ++ tailWord_2324847) baseStart_2324847 baseEnd_2324847 := by
    simpa [prefixWord, tailWord_2324847, baseEnd_2324847] using wordTrace_append hprefix tailTrace_2324847
  have hstable : (prefixWord ++ tailWord_2324847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324847).length < 2 ^ (prefixWord ++ tailWord_2324847).sum := by decide
  have hdescent : baseEnd_2324847 < baseStart_2324847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324868 : List Nat := [2, 3, 2, 1, 1, 2, 3, 3, 2, 2, 2]
def baseStart_2324868 : Nat := 118140960795 + 2324868 * 2 ^ 59
def prefixEnd_2324868 : Nat := 4983230072969 + 3 ^ 40 * 2324868 * 2
def baseEnd_2324868 : Nat := 1193774742257115176958133

theorem tailTrace_2324868 : CollatzResearch.WordTrace tailWord_2324868 prefixEnd_2324868 1193774742257115176958133 := by
  unfold tailWord_2324868
  simp only [CollatzResearch.WordTrace]
  refine ⟨42397451070703883344139629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56529934760938511125519505 42397451070703883344139629)
  ·
    refine ⟨15899044151513956254052361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42397451070703883344139629 15899044151513956254052361)
    ·
      refine ⟨11924283113635467190539271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15899044151513956254052361 11924283113635467190539271)
      ·
        refine ⟨17886424670453200785808907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11924283113635467190539271 17886424670453200785808907)
        ·
          refine ⟨26829637005679801178713361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17886424670453200785808907 26829637005679801178713361)
          ·
            refine ⟨20122227754259850884035021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26829637005679801178713361 20122227754259850884035021)
            ·
              refine ⟨7545835407847444081513133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20122227754259850884035021 7545835407847444081513133)
              ·
                refine ⟨2829688277942791530567425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7545835407847444081513133 2829688277942791530567425)
                ·
                  refine ⟨2122266208457093647925569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2829688277942791530567425 2122266208457093647925569)
                  ·
                    refine ⟨1591699656342820235944177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2122266208457093647925569 1591699656342820235944177)
                    ·
                      refine ⟨1193774742257115176958133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1591699656342820235944177 1193774742257115176958133)
                      ·
                        rfl

theorem cell23_2324868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_2324868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324868 prefixEnd_2324868 := by exact prefixLift 2324868
  have htrace : WordTrace (prefixWord ++ tailWord_2324868) baseStart_2324868 baseEnd_2324868 := by
    simpa [prefixWord, tailWord_2324868, baseEnd_2324868] using wordTrace_append hprefix tailTrace_2324868
  have hstable : (prefixWord ++ tailWord_2324868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324868).length < 2 ^ (prefixWord ++ tailWord_2324868).sum := by decide
  have hdescent : baseEnd_2324868 < baseStart_2324868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324887 : List Nat := [1, 1, 3, 3, 1, 1, 2, 3, 1, 7]
def baseStart_2324887 : Nat := 118140960795 + 2324887 * 2 ^ 59
def prefixEnd_2324887 : Nat := 4983230072969 + 3 ^ 40 * 2324887 * 2
def baseEnd_2324887 : Nat := 397928166129850200873515

theorem tailTrace_2324887 : CollatzResearch.WordTrace tailWord_2324887 prefixEnd_2324887 397928166129850200873515 := by
  unfold tailWord_2324887
  simp only [CollatzResearch.WordTrace]
  refine ⟨84795595128338932933220915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56530396752225955288813943 84795595128338932933220915)
  ·
    refine ⟨127193392692508399399831373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84795595128338932933220915 127193392692508399399831373)
    ·
      refine ⟨47697522259690649774936765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127193392692508399399831373 47697522259690649774936765)
      ·
        refine ⟨17886570847383993665601287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47697522259690649774936765 17886570847383993665601287)
        ·
          refine ⟨26829856271075990498401931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17886570847383993665601287 26829856271075990498401931)
          ·
            refine ⟨40244784406613985747602897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26829856271075990498401931 40244784406613985747602897)
            ·
              refine ⟨30183588304960489310702173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40244784406613985747602897 30183588304960489310702173)
              ·
                refine ⟨11318845614360183491513315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30183588304960489310702173 11318845614360183491513315)
                ·
                  refine ⟨16978268421540275237269973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11318845614360183491513315 16978268421540275237269973)
                  ·
                    refine ⟨397928166129850200873515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16978268421540275237269973 397928166129850200873515)
                    ·
                      rfl

theorem cell23_2324887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 7].length) (baseStart_2324887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324887 prefixEnd_2324887 := by exact prefixLift 2324887
  have htrace : WordTrace (prefixWord ++ tailWord_2324887) baseStart_2324887 baseEnd_2324887 := by
    simpa [prefixWord, tailWord_2324887, baseEnd_2324887] using wordTrace_append hprefix tailTrace_2324887
  have hstable : (prefixWord ++ tailWord_2324887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324887).length < 2 ^ (prefixWord ++ tailWord_2324887).sum := by decide
  have hdescent : baseEnd_2324887 < baseStart_2324887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324968 : List Nat := [2, 1, 4, 1, 1, 3, 2, 4, 1, 4]
def baseStart_2324968 : Nat := 118140960795 + 2324968 * 2 ^ 59
def prefixEnd_2324968 : Nat := 4983230072969 + 3 ^ 40 * 2324968 * 2
def baseEnd_2324968 : Nat := 397942030107521595235891

theorem tailTrace_2324968 : CollatzResearch.WordTrace tailWord_2324968 prefixEnd_2324968 397942030107521595235891 := by
  unfold tailWord_2324968
  simp only [CollatzResearch.WordTrace]
  refine ⟨42399274720522741883459779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56532366294030322511279705 42399274720522741883459779)
  ·
    refine ⟨63598912080784112825189669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42399274720522741883459779 63598912080784112825189669)
    ·
      refine ⟨11924796015147021154723063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63598912080784112825189669 11924796015147021154723063)
      ·
        refine ⟨17887194022720531732084595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11924796015147021154723063 17887194022720531732084595)
        ·
          refine ⟨26830791034080797598126893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17887194022720531732084595 26830791034080797598126893)
          ·
            refine ⟨10061546637780299099297585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26830791034080797598126893 10061546637780299099297585)
            ·
              refine ⟨7546159978335224324473189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10061546637780299099297585 7546159978335224324473189)
              ·
                refine ⟨1414904995937854560838723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7546159978335224324473189 1414904995937854560838723)
                ·
                  refine ⟨2122357493906781841258085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1414904995937854560838723 2122357493906781841258085)
                  ·
                    refine ⟨397942030107521595235891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2122357493906781841258085 397942030107521595235891)
                    ·
                      rfl

theorem cell23_2324968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_2324968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324968 prefixEnd_2324968 := by exact prefixLift 2324968
  have htrace : WordTrace (prefixWord ++ tailWord_2324968) baseStart_2324968 baseEnd_2324968 := by
    simpa [prefixWord, tailWord_2324968, baseEnd_2324968] using wordTrace_append hprefix tailTrace_2324968
  have hstable : (prefixWord ++ tailWord_2324968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324968).length < 2 ^ (prefixWord ++ tailWord_2324968).sum := by decide
  have hdescent : baseEnd_2324968 < baseStart_2324968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2324991 : List Nat := [1, 1, 2, 2, 1, 2, 3, 4, 3, 1, 3]
def baseStart_2324991 : Nat := 118140960795 + 2324991 * 2 ^ 59
def prefixEnd_2324991 : Nat := 4983230072969 + 3 ^ 40 * 2324991 * 2
def baseEnd_2324991 : Nat := 1193837900377618195720067

theorem tailTrace_2324991 : CollatzResearch.WordTrace tailWord_2324991 prefixEnd_2324991 1193837900377618195720067 := by
  unfold tailWord_2324991
  simp only [CollatzResearch.WordTrace]
  refine ⟨84799388319962158695006827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56532925546641439130004551 84799388319962158695006827)
  ·
    refine ⟨127199082479943238042510241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84799388319962158695006827 127199082479943238042510241)
    ·
      refine ⟨95399311859957428531882681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127199082479943238042510241 95399311859957428531882681)
      ·
        refine ⟨71549483894968071398912011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95399311859957428531882681 71549483894968071398912011)
        ·
          refine ⟨107324225842452107098368017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71549483894968071398912011 107324225842452107098368017)
          ·
            refine ⟨80493169381839080323776013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107324225842452107098368017 80493169381839080323776013)
            ·
              refine ⟨30184938518189655121416005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80493169381839080323776013 30184938518189655121416005)
              ·
                refine ⟨5659675972160560335265501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30184938518189655121416005 5659675972160560335265501)
                ·
                  refine ⟨2122378489560210125724563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5659675972160560335265501 2122378489560210125724563)
                  ·
                    refine ⟨3183567734340315188586845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2122378489560210125724563 3183567734340315188586845)
                    ·
                      refine ⟨1193837900377618195720067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3183567734340315188586845 1193837900377618195720067)
                      ·
                        rfl

theorem cell23_2324991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 3, 1, 3].length) (baseStart_2324991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2324991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2324991 prefixEnd_2324991 := by exact prefixLift 2324991
  have htrace : WordTrace (prefixWord ++ tailWord_2324991) baseStart_2324991 baseEnd_2324991 := by
    simpa [prefixWord, tailWord_2324991, baseEnd_2324991] using wordTrace_append hprefix tailTrace_2324991
  have hstable : (prefixWord ++ tailWord_2324991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2324991).length < 2 ^ (prefixWord ++ tailWord_2324991).sum := by decide
  have hdescent : baseEnd_2324991 < baseStart_2324991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2324991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325048 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 5, 2, 2]
def baseStart_2325048 : Nat := 118140960795 + 2325048 * 2 ^ 59
def prefixEnd_2325048 : Nat := 4983230072969 + 3 ^ 40 * 2325048 * 2
def baseEnd_2325048 : Nat := 1193867168774924472707305

theorem tailTrace_2325048 : CollatzResearch.WordTrace tailWord_2325048 prefixEnd_2325048 1193867168774924472707305 := by
  unfold tailWord_2325048
  simp only [CollatzResearch.WordTrace]
  refine ⟨42400733640377828714915899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56534311520503771619887865 42400733640377828714915899)
  ·
    refine ⟨63601100460566743072373849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42400733640377828714915899 63601100460566743072373849)
    ·
      refine ⟨47700825345425057304280387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63601100460566743072373849 47700825345425057304280387)
      ·
        refine ⟨71551238018137585956420581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47700825345425057304280387 71551238018137585956420581)
        ·
          refine ⟨13415857128400797366828859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71551238018137585956420581 13415857128400797366828859)
          ·
            refine ⟨20123785692601196050243289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13415857128400797366828859 20123785692601196050243289)
            ·
              refine ⟨15092839269450897037682467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20123785692601196050243289 15092839269450897037682467)
              ·
                refine ⟨22639258904176345556523701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15092839269450897037682467 22639258904176345556523701)
                ·
                  refine ⟨2122430522266532395924097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22639258904176345556523701 2122430522266532395924097)
                  ·
                    refine ⟨1591822891699899296943073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2122430522266532395924097 1591822891699899296943073)
                    ·
                      refine ⟨1193867168774924472707305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1591822891699899296943073 1193867168774924472707305)
                      ·
                        rfl

theorem cell23_2325048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 5, 2, 2].length) (baseStart_2325048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325048 prefixEnd_2325048 := by exact prefixLift 2325048
  have htrace : WordTrace (prefixWord ++ tailWord_2325048) baseStart_2325048 baseEnd_2325048 := by
    simpa [prefixWord, tailWord_2325048, baseEnd_2325048] using wordTrace_append hprefix tailTrace_2325048
  have hstable : (prefixWord ++ tailWord_2325048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325048).length < 2 ^ (prefixWord ++ tailWord_2325048).sum := by decide
  have hdescent : baseEnd_2325048 < baseStart_2325048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325061 : List Nat := [1, 3, 1, 1, 1, 6, 1, 2, 1, 2, 4]
def baseStart_2325061 : Nat := 118140960795 + 2325061 * 2 ^ 59
def prefixEnd_2325061 : Nat := 4983230072969 + 3 ^ 40 * 2325061 * 2
def baseEnd_2325061 : Nat := 1193873844023432921844745

theorem tailTrace_2325061 : CollatzResearch.WordTrace tailWord_2325061 prefixEnd_2325061 1193873844023432921844745 := by
  unfold tailWord_2325061
  simp only [CollatzResearch.WordTrace]
  refine ⟨84801941429708560650055037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56534627619805707100036691 84801941429708560650055037)
  ·
    refine ⟨31800728036140710243770639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84801941429708560650055037 31800728036140710243770639)
    ·
      refine ⟨47701092054211065365655959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31800728036140710243770639 47701092054211065365655959)
      ·
        refine ⟨71551638081316598048483939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47701092054211065365655959 71551638081316598048483939)
        ·
          refine ⟨107327457121974897072725909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71551638081316598048483939 107327457121974897072725909)
          ·
            refine ⟨5030974552592573300284027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 107327457121974897072725909 5030974552592573300284027)
            ·
              refine ⟨7546461828888859950426041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5030974552592573300284027 7546461828888859950426041)
              ·
                refine ⟨5659846371666644962819531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7546461828888859950426041 5659846371666644962819531)
                ·
                  refine ⟨8489769557499967444229297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5659846371666644962819531 8489769557499967444229297)
                  ·
                    refine ⟨6367327168124975583171973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8489769557499967444229297 6367327168124975583171973)
                    ·
                      refine ⟨1193873844023432921844745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6367327168124975583171973 1193873844023432921844745)
                      ·
                        rfl

theorem cell23_2325061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 2, 4].length) (baseStart_2325061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325061 prefixEnd_2325061 := by exact prefixLift 2325061
  have htrace : WordTrace (prefixWord ++ tailWord_2325061) baseStart_2325061 baseEnd_2325061 := by
    simpa [prefixWord, tailWord_2325061, baseEnd_2325061] using wordTrace_append hprefix tailTrace_2325061
  have hstable : (prefixWord ++ tailWord_2325061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325061).length < 2 ^ (prefixWord ++ tailWord_2325061).sum := by decide
  have hdescent : baseEnd_2325061 < baseStart_2325061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325062 : List Nat := [6, 1, 1, 1, 2, 2, 3, 1, 1, 5]
def baseStart_2325062 : Nat := 118140960795 + 2325062 * 2 ^ 59
def prefixEnd_2325062 : Nat := 4983230072969 + 3 ^ 40 * 2325062 * 2
def baseEnd_2325062 : Nat := 397958119168029139310747

theorem tailTrace_2325062 : CollatzResearch.WordTrace tailWord_2325062 prefixEnd_2325062 397958119168029139310747 := by
  unfold tailWord_2325062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2650061809459529306901295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 56534651935136625213894293 2650061809459529306901295)
  ·
    refine ⟨3975092714189293960351943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2650061809459529306901295 3975092714189293960351943)
    ·
      refine ⟨5962639071283940940527915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3975092714189293960351943 5962639071283940940527915)
      ·
        refine ⟨8943958606925911410791873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5962639071283940940527915 8943958606925911410791873)
        ·
          refine ⟨6707968955194433558093905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8943958606925911410791873 6707968955194433558093905)
          ·
            refine ⟨5030976716395825168570429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6707968955194433558093905 5030976716395825168570429)
            ·
              refine ⟨1886616268648434438213911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5030976716395825168570429 1886616268648434438213911)
              ·
                refine ⟨2829924402972651657320867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1886616268648434438213911 2829924402972651657320867)
                ·
                  refine ⟨4244886604458977485981301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2829924402972651657320867 4244886604458977485981301)
                  ·
                    refine ⟨397958119168029139310747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4244886604458977485981301 397958119168029139310747)
                    ·
                      rfl

theorem cell23_2325062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_2325062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325062 prefixEnd_2325062 := by exact prefixLift 2325062
  have htrace : WordTrace (prefixWord ++ tailWord_2325062) baseStart_2325062 baseEnd_2325062 := by
    simpa [prefixWord, tailWord_2325062, baseEnd_2325062] using wordTrace_append hprefix tailTrace_2325062
  have hstable : (prefixWord ++ tailWord_2325062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325062).length < 2 ^ (prefixWord ++ tailWord_2325062).sum := by decide
  have hdescent : baseEnd_2325062 < baseStart_2325062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325098 : List Nat := [3, 1, 3, 2, 1, 1, 4, 1, 1, 3, 3]
def baseStart_2325098 : Nat := 118140960795 + 2325098 * 2 ^ 59
def prefixEnd_2325098 : Nat := 4983230072969 + 3 ^ 40 * 2325098 * 2
def baseEnd_2325098 : Nat := 1193892842807649277082075

theorem tailTrace_2325098 : CollatzResearch.WordTrace tailWord_2325098 prefixEnd_2325098 1193892842807649277082075 := by
  unfold tailWord_2325098
  simp only [CollatzResearch.WordTrace]
  refine ⟨21200822732643628992287987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56535527287049677312767965 21200822732643628992287987)
  ·
    refine ⟨31801234098965443488431981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21200822732643628992287987 31801234098965443488431981)
    ·
      refine ⟨11925462787112041308161993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31801234098965443488431981 11925462787112041308161993)
      ·
        refine ⟨8944097090334030981121495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11925462787112041308161993 8944097090334030981121495)
        ·
          refine ⟨13416145635501046471682243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8944097090334030981121495 13416145635501046471682243)
          ·
            refine ⟨20124218453251569707523365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13416145635501046471682243 20124218453251569707523365)
            ·
              refine ⟨3773290959984669320160631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20124218453251569707523365 3773290959984669320160631)
              ·
                refine ⟨5659936439977003980240947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3773290959984669320160631 5659936439977003980240947)
                ·
                  refine ⟨8489904659965505970361421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5659936439977003980240947 8489904659965505970361421)
                  ·
                    refine ⟨3183714247487064738885533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8489904659965505970361421 3183714247487064738885533)
                    ·
                      refine ⟨1193892842807649277082075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3183714247487064738885533 1193892842807649277082075)
                      ·
                        rfl

theorem cell23_2325098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_2325098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325098 prefixEnd_2325098 := by exact prefixLift 2325098
  have htrace : WordTrace (prefixWord ++ tailWord_2325098) baseStart_2325098 baseEnd_2325098 := by
    simpa [prefixWord, tailWord_2325098, baseEnd_2325098] using wordTrace_append hprefix tailTrace_2325098
  have hstable : (prefixWord ++ tailWord_2325098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325098).length < 2 ^ (prefixWord ++ tailWord_2325098).sum := by decide
  have hdescent : baseEnd_2325098 < baseStart_2325098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325125 : List Nat := [1, 3, 1, 1, 4, 3, 1, 3, 1, 3, 2]
def baseStart_2325125 : Nat := 118140960795 + 2325125 * 2 ^ 59
def prefixEnd_2325125 : Nat := 4983230072969 + 3 ^ 40 * 2325125 * 2
def baseEnd_2325125 : Nat := 1193906706785320671444451

theorem tailTrace_2325125 : CollatzResearch.WordTrace tailWord_2325125 prefixEnd_2325125 1193906706785320671444451 := by
  unfold tailWord_2325125
  simp only [CollatzResearch.WordTrace]
  refine ⟨84804275701476699580384829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56536183800984466386923219 84804275701476699580384829)
  ·
    refine ⟨31801603388053762342644311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84804275701476699580384829 31801603388053762342644311)
    ·
      refine ⟨47702405082080643513966467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31801603388053762342644311 47702405082080643513966467)
      ·
        refine ⟨71553607623120965270949701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47702405082080643513966467 71553607623120965270949701)
        ·
          refine ⟨13416301429335180988303069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71553607623120965270949701 13416301429335180988303069)
          ·
            refine ⟨5031113036000692870613651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13416301429335180988303069 5031113036000692870613651)
            ·
              refine ⟨7546669554001039305920477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5031113036000692870613651 7546669554001039305920477)
              ·
                refine ⟨2830001082750389739720179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7546669554001039305920477 2830001082750389739720179)
                ·
                  refine ⟨4245001624125584609580269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2830001082750389739720179 4245001624125584609580269)
                  ·
                    refine ⟨1591875609047094228592601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4245001624125584609580269 1591875609047094228592601)
                    ·
                      refine ⟨1193906706785320671444451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1591875609047094228592601 1193906706785320671444451)
                      ·
                        rfl

theorem cell23_2325125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 1, 3, 2].length) (baseStart_2325125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325125 prefixEnd_2325125 := by exact prefixLift 2325125
  have htrace : WordTrace (prefixWord ++ tailWord_2325125) baseStart_2325125 baseEnd_2325125 := by
    simpa [prefixWord, tailWord_2325125, baseEnd_2325125] using wordTrace_append hprefix tailTrace_2325125
  have hstable : (prefixWord ++ tailWord_2325125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325125).length < 2 ^ (prefixWord ++ tailWord_2325125).sum := by decide
  have hdescent : baseEnd_2325125 < baseStart_2325125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325159 : List Nat := [1, 1, 6, 3, 1, 1, 2, 2, 1, 3, 2]
def baseStart_2325159 : Nat := 118140960795 + 2325159 * 2 ^ 59
def prefixEnd_2325159 : Nat := 4983230072969 + 3 ^ 40 * 2325159 * 2
def baseEnd_2325159 : Nat := 1193924165127573538419295

theorem tailTrace_2325159 : CollatzResearch.WordTrace tailWord_2325159 prefixEnd_2325159 1193924165127573538419295 := by
  unfold tailWord_2325159
  simp only [CollatzResearch.WordTrace]
  refine ⟨84805515783353523387122531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56537010522235682258081687 84805515783353523387122531)
  ·
    refine ⟨127208273675030285080683797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84805515783353523387122531 127208273675030285080683797)
    ·
      refine ⟨5962887828517044613157053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 127208273675030285080683797 5962887828517044613157053)
      ·
        refine ⟨2236082935693891729933895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5962887828517044613157053 2236082935693891729933895)
        ·
          refine ⟨3354124403540837594900843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2236082935693891729933895 3354124403540837594900843)
          ·
            refine ⟨5031186605311256392351265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3354124403540837594900843 5031186605311256392351265)
            ·
              refine ⟨3773389953983442294263449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5031186605311256392351265 3773389953983442294263449)
              ·
                refine ⟨2830042465487581720697587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3773389953983442294263449 2830042465487581720697587)
                ·
                  refine ⟨4245063698231372581046381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2830042465487581720697587 4245063698231372581046381)
                  ·
                    refine ⟨1591898886836764717892393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4245063698231372581046381 1591898886836764717892393)
                    ·
                      refine ⟨1193924165127573538419295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1591898886836764717892393 1193924165127573538419295)
                      ·
                        rfl

theorem cell23_2325159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_2325159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325159 prefixEnd_2325159 := by exact prefixLift 2325159
  have htrace : WordTrace (prefixWord ++ tailWord_2325159) baseStart_2325159 baseEnd_2325159 := by
    simpa [prefixWord, tailWord_2325159, baseEnd_2325159] using wordTrace_append hprefix tailTrace_2325159
  have hstable : (prefixWord ++ tailWord_2325159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325159).length < 2 ^ (prefixWord ++ tailWord_2325159).sum := by decide
  have hdescent : baseEnd_2325159 < baseStart_2325159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325201 : List Nat := [1, 2, 2, 1, 2, 3, 3, 1, 1, 2, 5]
def baseStart_2325201 : Nat := 118140960795 + 2325201 * 2 ^ 59
def prefixEnd_2325201 : Nat := 4983230072969 + 3 ^ 40 * 2325201 * 2
def baseEnd_2325201 : Nat := 1193945731315062374094101

theorem tailTrace_2325201 : CollatzResearch.WordTrace tailWord_2325201 prefixEnd_2325201 1193945731315062374094101 := by
  unfold tailWord_2325201
  simp only [CollatzResearch.WordTrace]
  refine ⟨84807047649201364560151457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56538031766134243040100971 84807047649201364560151457)
  ·
    refine ⟨63605285736901023420113593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84807047649201364560151457 63605285736901023420113593)
    ·
      refine ⟨47703964302675767565085195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63605285736901023420113593 47703964302675767565085195)
      ·
        refine ⟨71555946454013651347627793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47703964302675767565085195 71555946454013651347627793)
        ·
          refine ⟨53666959840510238510720845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71555946454013651347627793 53666959840510238510720845)
          ·
            refine ⟨20125109940191339441520317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53666959840510238510720845 20125109940191339441520317)
            ·
              refine ⟨7546916227571752290570119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20125109940191339441520317 7546916227571752290570119)
              ·
                refine ⟨11320374341357628435855179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7546916227571752290570119 11320374341357628435855179)
                ·
                  refine ⟨16980561512036442653782769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11320374341357628435855179 16980561512036442653782769)
                  ·
                    refine ⟨12735421134027331990337077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16980561512036442653782769 12735421134027331990337077)
                    ·
                      refine ⟨1193945731315062374094101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12735421134027331990337077 1193945731315062374094101)
                      ·
                        rfl

theorem cell23_2325201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_2325201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325201 prefixEnd_2325201 := by exact prefixLift 2325201
  have htrace : WordTrace (prefixWord ++ tailWord_2325201) baseStart_2325201 baseEnd_2325201 := by
    simpa [prefixWord, tailWord_2325201, baseEnd_2325201] using wordTrace_append hprefix tailTrace_2325201
  have hstable : (prefixWord ++ tailWord_2325201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325201).length < 2 ^ (prefixWord ++ tailWord_2325201).sum := by decide
  have hdescent : baseEnd_2325201 < baseStart_2325201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325228 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 4, 4, 2]
def baseStart_2325228 : Nat := 118140960795 + 2325228 * 2 ^ 59
def prefixEnd_2325228 : Nat := 4983230072969 + 3 ^ 40 * 2325228 * 2
def baseEnd_2325228 : Nat := 1193959595292733768456477

theorem tailTrace_2325228 : CollatzResearch.WordTrace tailWord_2325228 prefixEnd_2325228 1193959595292733768456477 := by
  unfold tailWord_2325228
  simp only [CollatzResearch.WordTrace]
  refine ⟨42404016210051774085692169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56538688280069032114256225 42404016210051774085692169)
  ·
    refine ⟨31803012157538830564269127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42404016210051774085692169 31803012157538830564269127)
    ·
      refine ⟨47704518236308245846403691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31803012157538830564269127 47704518236308245846403691)
      ·
        refine ⟨71556777354462368769605537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47704518236308245846403691 71556777354462368769605537)
        ·
          refine ⟨53667583015846776577204153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71556777354462368769605537 53667583015846776577204153)
          ·
            refine ⟨40250687261885082432903115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53667583015846776577204153 40250687261885082432903115)
            ·
              refine ⟨60376030892827623649354673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40250687261885082432903115 60376030892827623649354673)
              ·
                refine ⟨45282023169620717737016005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60376030892827623649354673 45282023169620717737016005)
                ·
                  refine ⟨8490379344303884575690501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45282023169620717737016005 8490379344303884575690501)
                  ·
                    refine ⟨1591946127056978357941969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8490379344303884575690501 1591946127056978357941969)
                    ·
                      refine ⟨1193959595292733768456477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1591946127056978357941969 1193959595292733768456477)
                      ·
                        rfl

theorem cell23_2325228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 4, 2].length) (baseStart_2325228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325228 prefixEnd_2325228 := by exact prefixLift 2325228
  have htrace : WordTrace (prefixWord ++ tailWord_2325228) baseStart_2325228 baseEnd_2325228 := by
    simpa [prefixWord, tailWord_2325228, baseEnd_2325228] using wordTrace_append hprefix tailTrace_2325228
  have hstable : (prefixWord ++ tailWord_2325228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325228).length < 2 ^ (prefixWord ++ tailWord_2325228).sum := by decide
  have hdescent : baseEnd_2325228 < baseStart_2325228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325282 : List Nat := [3, 3, 1, 1, 2, 4, 1, 1, 2, 2, 3]
def baseStart_2325282 : Nat := 118140960795 + 2325282 * 2 ^ 59
def prefixEnd_2325282 : Nat := 4983230072969 + 3 ^ 40 * 2325282 * 2
def baseEnd_2325282 : Nat := 1193987323248076557181229

theorem tailTrace_2325282 : CollatzResearch.WordTrace tailWord_2325282 prefixEnd_2325282 1193987323248076557181229 := by
  unfold tailWord_2325282
  simp only [CollatzResearch.WordTrace]
  refine ⟨21202500490476978848462525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56540001307938610262566733 21202500490476978848462525)
  ·
    refine ⟨7950937683928867068173447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21202500490476978848462525 7950937683928867068173447)
    ·
      refine ⟨11926406525893300602260171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7950937683928867068173447 11926406525893300602260171)
      ·
        refine ⟨17889609788839950903390257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11926406525893300602260171 17889609788839950903390257)
        ·
          refine ⟨13417207341629963177542693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17889609788839950903390257 13417207341629963177542693)
          ·
            refine ⟨2515726376555618095789255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13417207341629963177542693 2515726376555618095789255)
            ·
              refine ⟨3773589564833427143683883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2515726376555618095789255 3773589564833427143683883)
              ·
                refine ⟨5660384347250140715525825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3773589564833427143683883 5660384347250140715525825)
                ·
                  refine ⟨4245288260437605536644369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5660384347250140715525825 4245288260437605536644369)
                  ·
                    refine ⟨3183966195328204152483277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4245288260437605536644369 3183966195328204152483277)
                    ·
                      refine ⟨1193987323248076557181229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3183966195328204152483277 1193987323248076557181229)
                      ·
                        rfl

theorem cell23_2325282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_2325282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325282 prefixEnd_2325282 := by exact prefixLift 2325282
  have htrace : WordTrace (prefixWord ++ tailWord_2325282) baseStart_2325282 baseEnd_2325282 := by
    simpa [prefixWord, tailWord_2325282, baseEnd_2325282] using wordTrace_append hprefix tailTrace_2325282
  have hstable : (prefixWord ++ tailWord_2325282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325282).length < 2 ^ (prefixWord ++ tailWord_2325282).sum := by decide
  have hdescent : baseEnd_2325282 < baseStart_2325282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325328 : List Nat := [2, 1, 1, 1, 1, 4, 5, 1, 1, 6]
def baseStart_2325328 : Nat := 118140960795 + 2325328 * 2 ^ 59
def prefixEnd_2325328 : Nat := 4983230072969 + 3 ^ 40 * 2325328 * 2
def baseEnd_2325328 : Nat := 398003647786061125735339

theorem tailTrace_2325328 : CollatzResearch.WordTrace tailWord_2325328 prefixEnd_2325328 398003647786061125735339 := by
  unfold tailWord_2325328
  simp only [CollatzResearch.WordTrace]
  refine ⟨42405839859870632625012319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56541119813160843500016425 42405839859870632625012319)
  ·
    refine ⟨63608759789805948937518479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42405839859870632625012319 63608759789805948937518479)
    ·
      refine ⟨95413139684708923406277719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63608759789805948937518479 95413139684708923406277719)
      ·
        refine ⟨143119709527063385109416579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95413139684708923406277719 143119709527063385109416579)
        ·
          refine ⟨214679564290595077664124869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143119709527063385109416579 214679564290595077664124869)
          ·
            refine ⟨40252418304486577062023413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 214679564290595077664124869 40252418304486577062023413)
            ·
              refine ⟨3773664216045616599564695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40252418304486577062023413 3773664216045616599564695)
              ·
                refine ⟨5660496324068424899347043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3773664216045616599564695 5660496324068424899347043)
                ·
                  refine ⟨8490744486102637349020565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5660496324068424899347043 8490744486102637349020565)
                  ·
                    refine ⟨398003647786061125735339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8490744486102637349020565 398003647786061125735339)
                    ·
                      rfl

theorem cell23_2325328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 1, 6].length) (baseStart_2325328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325328 prefixEnd_2325328 := by exact prefixLift 2325328
  have htrace : WordTrace (prefixWord ++ tailWord_2325328) baseStart_2325328 baseEnd_2325328 := by
    simpa [prefixWord, tailWord_2325328, baseEnd_2325328] using wordTrace_append hprefix tailTrace_2325328
  have hstable : (prefixWord ++ tailWord_2325328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325328).length < 2 ^ (prefixWord ++ tailWord_2325328).sum := by decide
  have hdescent : baseEnd_2325328 < baseStart_2325328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325332 : List Nat := [2, 4, 1, 1, 4, 1, 2, 2, 1, 5]
def baseStart_2325332 : Nat := 118140960795 + 2325332 * 2 ^ 59
def prefixEnd_2325332 : Nat := 4983230072969 + 3 ^ 40 * 2325332 * 2
def baseEnd_2325332 : Nat := 398004332426933787185333

theorem tailTrace_2325332 : CollatzResearch.WordTrace tailWord_2325332 prefixEnd_2325332 398004332426933787185333 := by
  unfold tailWord_2325332
  simp only [CollatzResearch.WordTrace]
  refine ⟨42405912805863386966585125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56541217074484515955446833 42405912805863386966585125)
  ·
    refine ⟨7951108651099385056234711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42405912805863386966585125 7951108651099385056234711)
    ·
      refine ⟨11926662976649077584352067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7951108651099385056234711 11926662976649077584352067)
      ·
        refine ⟨17889994464973616376528101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11926662976649077584352067 17889994464973616376528101)
        ·
          refine ⟨3354373962182553070599019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17889994464973616376528101 3354373962182553070599019)
          ·
            refine ⟨5031560943273829605898529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3354373962182553070599019 5031560943273829605898529)
            ·
              refine ⟨3773670707455372204423897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5031560943273829605898529 3773670707455372204423897)
              ·
                refine ⟨2830253030591529153317923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3773670707455372204423897 2830253030591529153317923)
                ·
                  refine ⟨4245379545887293729976885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2830253030591529153317923 4245379545887293729976885)
                  ·
                    refine ⟨398004332426933787185333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4245379545887293729976885 398004332426933787185333)
                    ·
                      rfl

theorem cell23_2325332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_2325332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325332 prefixEnd_2325332 := by exact prefixLift 2325332
  have htrace : WordTrace (prefixWord ++ tailWord_2325332) baseStart_2325332 baseEnd_2325332 := by
    simpa [prefixWord, tailWord_2325332, baseEnd_2325332] using wordTrace_append hprefix tailTrace_2325332
  have hstable : (prefixWord ++ tailWord_2325332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325332).length < 2 ^ (prefixWord ++ tailWord_2325332).sum := by decide
  have hdescent : baseEnd_2325332 < baseStart_2325332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325335 : List Nat := [1, 1, 3, 2, 4, 1, 1, 4, 1, 1, 4]
def baseStart_2325335 : Nat := 118140960795 + 2325335 * 2 ^ 59
def prefixEnd_2325335 : Nat := 4983230072969 + 3 ^ 40 * 2325335 * 2
def baseEnd_2325335 : Nat := 1194014537722764849818485

theorem tailTrace_2325335 : CollatzResearch.WordTrace tailWord_2325335 prefixEnd_2325335 1194014537722764849818485 := by
  unfold tailWord_2325335
  simp only [CollatzResearch.WordTrace]
  refine ⟨84811935030715905445529459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56541290020477270297019639 84811935030715905445529459)
  ·
    refine ⟨127217902546073858168294189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84811935030715905445529459 127217902546073858168294189)
    ·
      refine ⟨47706713454777696813110321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127217902546073858168294189 47706713454777696813110321)
      ·
        refine ⟨35780035091083272609832741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47706713454777696813110321 35780035091083272609832741)
        ·
          refine ⟨6708756579578113614343639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35780035091083272609832741 6708756579578113614343639)
          ·
            refine ⟨10063134869367170421515459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6708756579578113614343639 10063134869367170421515459)
            ·
              refine ⟨15094702304050755632273189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10063134869367170421515459 15094702304050755632273189)
              ·
                refine ⟨2830256682009516681051223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15094702304050755632273189 2830256682009516681051223)
                ·
                  refine ⟨4245385023014275021576835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2830256682009516681051223 4245385023014275021576835)
                  ·
                    refine ⟨6368077534521412532365253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4245385023014275021576835 6368077534521412532365253)
                    ·
                      refine ⟨1194014537722764849818485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6368077534521412532365253 1194014537722764849818485)
                      ·
                        rfl

theorem cell23_2325335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_2325335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325335 prefixEnd_2325335 := by exact prefixLift 2325335
  have htrace : WordTrace (prefixWord ++ tailWord_2325335) baseStart_2325335 baseEnd_2325335 := by
    simpa [prefixWord, tailWord_2325335, baseEnd_2325335] using wordTrace_append hprefix tailTrace_2325335
  have hstable : (prefixWord ++ tailWord_2325335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325335).length < 2 ^ (prefixWord ++ tailWord_2325335).sum := by decide
  have hdescent : baseEnd_2325335 < baseStart_2325335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325355 : List Nat := [1, 1, 1, 1, 2, 2, 6, 3, 1, 2, 3]
def baseStart_2325355 : Nat := 118140960795 + 2325355 * 2 ^ 59
def prefixEnd_2325355 : Nat := 4983230072969 + 3 ^ 40 * 2325355 * 2
def baseEnd_2325355 : Nat := 1194024807335854771568393

theorem tailTrace_2325355 : CollatzResearch.WordTrace tailWord_2325355 prefixEnd_2325355 1194024807335854771568393 := by
  unfold tailWord_2325355
  simp only [CollatzResearch.WordTrace]
  refine ⟨84812664490643448861257519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56541776327095632574171679 84812664490643448861257519)
  ·
    refine ⟨127218996735965173291886279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84812664490643448861257519 127218996735965173291886279)
    ·
      refine ⟨190828495103947759937829419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127218996735965173291886279 190828495103947759937829419)
      ·
        refine ⟨286242742655921639906744129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190828495103947759937829419 286242742655921639906744129)
        ·
          refine ⟨214682056991941229930058097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286242742655921639906744129 214682056991941229930058097)
          ·
            refine ⟨161011542743955922447543573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214682056991941229930058097 161011542743955922447543573)
            ·
              refine ⟨7547416066122933864728605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 161011542743955922447543573 7547416066122933864728605)
              ·
                refine ⟨2830281024796100199273227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7547416066122933864728605 2830281024796100199273227)
                ·
                  refine ⟨4245421537194150298909841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2830281024796100199273227 4245421537194150298909841)
                  ·
                    refine ⟨3184066152895612724182381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4245421537194150298909841 3184066152895612724182381)
                    ·
                      refine ⟨1194024807335854771568393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3184066152895612724182381 1194024807335854771568393)
                      ·
                        rfl

theorem cell23_2325355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 2, 3].length) (baseStart_2325355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325355 prefixEnd_2325355 := by exact prefixLift 2325355
  have htrace : WordTrace (prefixWord ++ tailWord_2325355) baseStart_2325355 baseEnd_2325355 := by
    simpa [prefixWord, tailWord_2325355, baseEnd_2325355] using wordTrace_append hprefix tailTrace_2325355
  have hstable : (prefixWord ++ tailWord_2325355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325355).length < 2 ^ (prefixWord ++ tailWord_2325355).sum := by decide
  have hdescent : baseEnd_2325355 < baseStart_2325355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325368 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 5, 3, 3]
def baseStart_2325368 : Nat := 118140960795 + 2325368 * 2 ^ 59
def prefixEnd_2325368 : Nat := 4983230072969 + 3 ^ 40 * 2325368 * 2
def baseEnd_2325368 : Nat := 1194031482584363220705833

theorem tailTrace_2325368 : CollatzResearch.WordTrace tailWord_2325368 prefixEnd_2325368 1194031482584363220705833 := by
  unfold tailWord_2325368
  simp only [CollatzResearch.WordTrace]
  refine ⟨42406569319798176040740379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56542092426397568054320505 42406569319798176040740379)
  ·
    refine ⟨63609853979697264061110569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42406569319798176040740379 63609853979697264061110569)
    ·
      refine ⟨47707390484772948045832927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63609853979697264061110569 47707390484772948045832927)
      ·
        refine ⟨71561085727159422068749391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47707390484772948045832927 71561085727159422068749391)
        ·
          refine ⟨107341628590739133103124087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71561085727159422068749391 107341628590739133103124087)
          ·
            refine ⟨161012442886108699654686131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107341628590739133103124087 161012442886108699654686131)
            ·
              refine ⟨241518664329163049482029197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161012442886108699654686131 241518664329163049482029197)
              ·
                refine ⟨90569499123436143555760949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 241518664329163049482029197 90569499123436143555760949)
                ·
                  refine ⟨8490890542822138458352589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90569499123436143555760949 8490890542822138458352589)
                  ·
                    refine ⟨3184083953558301921882221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8490890542822138458352589 3184083953558301921882221)
                    ·
                      refine ⟨1194031482584363220705833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3184083953558301921882221 1194031482584363220705833)
                      ·
                        rfl

theorem cell23_2325368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 5, 3, 3].length) (baseStart_2325368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325368 prefixEnd_2325368 := by exact prefixLift 2325368
  have htrace : WordTrace (prefixWord ++ tailWord_2325368) baseStart_2325368 baseEnd_2325368 := by
    simpa [prefixWord, tailWord_2325368, baseEnd_2325368] using wordTrace_append hprefix tailTrace_2325368
  have hstable : (prefixWord ++ tailWord_2325368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325368).length < 2 ^ (prefixWord ++ tailWord_2325368).sum := by decide
  have hdescent : baseEnd_2325368 < baseStart_2325368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325369 : List Nat := [1, 2, 1, 3, 2, 5, 1, 1, 3, 2, 2]
def baseStart_2325369 : Nat := 118140960795 + 2325369 * 2 ^ 59
def prefixEnd_2325369 : Nat := 4983230072969 + 3 ^ 40 * 2325369 * 2
def baseEnd_2325369 : Nat := 1194031996065017716793329

theorem tailTrace_2325369 : CollatzResearch.WordTrace tailWord_2325369 prefixEnd_2325369 1194031996065017716793329 := by
  unfold tailWord_2325369
  simp only [CollatzResearch.WordTrace]
  refine ⟨84813175112592729252267161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56542116741728486168178107 84813175112592729252267161)
  ·
    refine ⟨63609881334444546939200371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84813175112592729252267161 63609881334444546939200371)
    ·
      refine ⟨95414822001666820408800557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63609881334444546939200371 95414822001666820408800557)
      ·
        refine ⟨35780558250625057653300209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95414822001666820408800557 35780558250625057653300209)
        ·
          refine ⟨26835418687968793239975157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35780558250625057653300209 26835418687968793239975157)
          ·
            refine ⟨2515820501997074366247671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26835418687968793239975157 2515820501997074366247671)
            ·
              refine ⟨3773730752995611549371507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2515820501997074366247671 3773730752995611549371507)
              ·
                refine ⟨5660596129493417324057261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3773730752995611549371507 5660596129493417324057261)
                ·
                  refine ⟨2122723548560031496521473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5660596129493417324057261 2122723548560031496521473)
                  ·
                    refine ⟨1592042661420023622391105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2122723548560031496521473 1592042661420023622391105)
                    ·
                      refine ⟨1194031996065017716793329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1592042661420023622391105 1194031996065017716793329)
                      ·
                        rfl

theorem cell23_2325369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 3, 2, 2].length) (baseStart_2325369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325369 prefixEnd_2325369 := by exact prefixLift 2325369
  have htrace : WordTrace (prefixWord ++ tailWord_2325369) baseStart_2325369 baseEnd_2325369 := by
    simpa [prefixWord, tailWord_2325369, baseEnd_2325369] using wordTrace_append hprefix tailTrace_2325369
  have hstable : (prefixWord ++ tailWord_2325369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325369).length < 2 ^ (prefixWord ++ tailWord_2325369).sum := by decide
  have hdescent : baseEnd_2325369 < baseStart_2325369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325402 : List Nat := [3, 1, 1, 4, 3, 1, 1, 2, 1, 3, 3]
def baseStart_2325402 : Nat := 118140960795 + 2325402 * 2 ^ 59
def prefixEnd_2325402 : Nat := 4983230072969 + 3 ^ 40 * 2325402 * 2
def baseEnd_2325402 : Nat := 1194048940926616087680677

theorem tailTrace_2325402 : CollatzResearch.WordTrace tailWord_2325402 prefixEnd_2325402 1194048940926616087680677 := by
  unfold tailWord_2325402
  simp only [CollatzResearch.WordTrace]
  refine ⟨21203594680368293972054615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56542919147648783925478973 21203594680368293972054615)
  ·
    refine ⟨31805392020552440958081923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21203594680368293972054615 31805392020552440958081923)
    ·
      refine ⟨47708088030828661437122885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31805392020552440958081923 47708088030828661437122885)
      ·
        refine ⟨8945266505780374019460541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47708088030828661437122885 8945266505780374019460541)
        ·
          refine ⟨3354474939667640257297703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8945266505780374019460541 3354474939667640257297703)
          ·
            refine ⟨5031712409501460385946555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3354474939667640257297703 5031712409501460385946555)
            ·
              refine ⟨7547568614252190578919833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5031712409501460385946555 7547568614252190578919833)
              ·
                refine ⟨5660676460689142934189875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7547568614252190578919833 5660676460689142934189875)
                ·
                  refine ⟨8491014691033714401284813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5660676460689142934189875 8491014691033714401284813)
                  ·
                    refine ⟨3184130509137642900481805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8491014691033714401284813 3184130509137642900481805)
                    ·
                      refine ⟨1194048940926616087680677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3184130509137642900481805 1194048940926616087680677)
                      ·
                        rfl

theorem cell23_2325402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_2325402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325402 prefixEnd_2325402 := by exact prefixLift 2325402
  have htrace : WordTrace (prefixWord ++ tailWord_2325402) baseStart_2325402 baseEnd_2325402 := by
    simpa [prefixWord, tailWord_2325402, baseEnd_2325402] using wordTrace_append hprefix tailTrace_2325402
  have hstable : (prefixWord ++ tailWord_2325402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325402).length < 2 ^ (prefixWord ++ tailWord_2325402).sum := by decide
  have hdescent : baseEnd_2325402 < baseStart_2325402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325475 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 4, 3, 3]
def baseStart_2325475 : Nat := 118140960795 + 2325475 * 2 ^ 59
def prefixEnd_2325475 : Nat := 4983230072969 + 3 ^ 40 * 2325475 * 2
def baseEnd_2325475 : Nat := 1194086425014394302067841

theorem tailTrace_2325475 : CollatzResearch.WordTrace tailWord_2325475 prefixEnd_2325475 1194086425014394302067841 := by
  unfold tailWord_2325475
  simp only [CollatzResearch.WordTrace]
  refine ⟨84817041250208709355625879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56544694166805806237083919 84817041250208709355625879)
  ·
    refine ⟨127225561875313064033438819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84817041250208709355625879 127225561875313064033438819)
    ·
      refine ⟨190838342812969596050158229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127225561875313064033438819 190838342812969596050158229)
      ·
        refine ⟨8945547319357949814851167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 190838342812969596050158229 8945547319357949814851167)
        ·
          refine ⟨13418320979036924722276751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8945547319357949814851167 13418320979036924722276751)
          ·
            refine ⟨20127481468555387083415127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13418320979036924722276751 20127481468555387083415127)
            ·
              refine ⟨30191222202833080625122691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20127481468555387083415127 30191222202833080625122691)
              ·
                refine ⟨45286833304249620937684037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30191222202833080625122691 45286833304249620937684037)
                ·
                  refine ⟨8491281244546803925815757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45286833304249620937684037 8491281244546803925815757)
                  ·
                    refine ⟨3184230466705051472180909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8491281244546803925815757 3184230466705051472180909)
                    ·
                      refine ⟨1194086425014394302067841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3184230466705051472180909 1194086425014394302067841)
                      ·
                        rfl

theorem cell23_2325475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_2325475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325475 prefixEnd_2325475 := by exact prefixLift 2325475
  have htrace : WordTrace (prefixWord ++ tailWord_2325475) baseStart_2325475 baseEnd_2325475 := by
    simpa [prefixWord, tailWord_2325475, baseEnd_2325475] using wordTrace_append hprefix tailTrace_2325475
  have hstable : (prefixWord ++ tailWord_2325475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325475).length < 2 ^ (prefixWord ++ tailWord_2325475).sum := by decide
  have hdescent : baseEnd_2325475 < baseStart_2325475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325482 : List Nat := [3, 1, 3, 1, 2, 2, 2, 4, 5]
def baseStart_2325482 : Nat := 118140960795 + 2325482 * 2 ^ 59
def prefixEnd_2325482 : Nat := 4983230072969 + 3 ^ 40 * 2325482 * 2
def baseEnd_2325482 : Nat := 132676668819886197186701

theorem tailTrace_2325482 : CollatzResearch.WordTrace tailWord_2325482 prefixEnd_2325482 132676668819886197186701 := by
  unfold tailWord_2325482
  simp only [CollatzResearch.WordTrace]
  refine ⟨21204324140295837387782675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56544864374122233034087133 21204324140295837387782675)
  ·
    refine ⟨31806486210443756081674013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21204324140295837387782675 31806486210443756081674013)
    ·
      refine ⟨11927432328916408530627755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31806486210443756081674013 11927432328916408530627755)
      ·
        refine ⟨17891148493374612795941633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11927432328916408530627755 17891148493374612795941633)
        ·
          refine ⟨13418361370030959596956225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17891148493374612795941633 13418361370030959596956225)
          ·
            refine ⟨10063771027523219697717169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13418361370030959596956225 10063771027523219697717169)
            ·
              refine ⟨7547828270642414773287877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10063771027523219697717169 7547828270642414773287877)
              ·
                refine ⟨1415217800745452769991477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7547828270642414773287877 1415217800745452769991477)
                ·
                  refine ⟨132676668819886197186701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1415217800745452769991477 132676668819886197186701)
                  ·
                    rfl

theorem cell23_2325482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 4, 5].length) (baseStart_2325482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325482 prefixEnd_2325482 := by exact prefixLift 2325482
  have htrace : WordTrace (prefixWord ++ tailWord_2325482) baseStart_2325482 baseEnd_2325482 := by
    simpa [prefixWord, tailWord_2325482, baseEnd_2325482] using wordTrace_append hprefix tailTrace_2325482
  have hstable : (prefixWord ++ tailWord_2325482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325482).length < 2 ^ (prefixWord ++ tailWord_2325482).sum := by decide
  have hdescent : baseEnd_2325482 < baseStart_2325482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325488 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 7]
def baseStart_2325488 : Nat := 118140960795 + 2325488 * 2 ^ 59
def prefixEnd_2325488 : Nat := 4983230072969 + 3 ^ 40 * 2325488 * 2
def baseEnd_2325488 : Nat := 1194093100262902751205281

theorem tailTrace_2325488 : CollatzResearch.WordTrace tailWord_2325488 prefixEnd_2325488 1194093100262902751205281 := by
  unfold tailWord_2325488
  simp only [CollatzResearch.WordTrace]
  refine ⟨42408757699580806287924559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56545010266107741717232745 42408757699580806287924559)
  ·
    refine ⟨63613136549371209431886839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42408757699580806287924559 63613136549371209431886839)
    ·
      refine ⟨95419704824056814147830259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63613136549371209431886839 95419704824056814147830259)
      ·
        refine ⟨143129557236085221221745389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95419704824056814147830259 143129557236085221221745389)
        ·
          refine ⟨53673583963531957958154521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143129557236085221221745389 53673583963531957958154521)
          ·
            refine ⟨40255187972648968468615891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53673583963531957958154521 40255187972648968468615891)
            ·
              refine ⟨60382781958973452702923837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40255187972648968468615891 60382781958973452702923837)
              ·
                refine ⟨22643543234615044763596439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60382781958973452702923837 22643543234615044763596439)
                ·
                  refine ⟨33965314851922567145394659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22643543234615044763596439 33965314851922567145394659)
                  ·
                    refine ⟨50947972277883850718091989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33965314851922567145394659 50947972277883850718091989)
                    ·
                      refine ⟨1194093100262902751205281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 50947972277883850718091989 1194093100262902751205281)
                      ·
                        rfl

theorem cell23_2325488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 7].length) (baseStart_2325488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325488 prefixEnd_2325488 := by exact prefixLift 2325488
  have htrace : WordTrace (prefixWord ++ tailWord_2325488) baseStart_2325488 baseEnd_2325488 := by
    simpa [prefixWord, tailWord_2325488, baseEnd_2325488] using wordTrace_append hprefix tailTrace_2325488
  have hstable : (prefixWord ++ tailWord_2325488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325488).length < 2 ^ (prefixWord ++ tailWord_2325488).sum := by decide
  have hdescent : baseEnd_2325488 < baseStart_2325488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325493 : List Nat := [1, 3, 5, 2, 1, 2, 1, 1, 1, 4, 2]
def baseStart_2325493 : Nat := 118140960795 + 2325493 * 2 ^ 59
def prefixEnd_2325493 : Nat := 4983230072969 + 3 ^ 40 * 2325493 * 2
def baseEnd_2325493 : Nat := 1194095667666175231642759

theorem tailTrace_2325493 : CollatzResearch.WordTrace tailWord_2325493 prefixEnd_2325493 1194095667666175231642759 := by
  unfold tailWord_2325493
  simp only [CollatzResearch.WordTrace]
  refine ⟨84817697764143498429781133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56545131842762332286520755 84817697764143498429781133)
  ·
    refine ⟨31806636661553811911167925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84817697764143498429781133 31806636661553811911167925)
    ·
      refine ⟨2981872187020669866671993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31806636661553811911167925 2981872187020669866671993)
      ·
        refine ⟨2236404140265502400003995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2981872187020669866671993 2236404140265502400003995)
        ·
          refine ⟨3354606210398253600005993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2236404140265502400003995 3354606210398253600005993)
          ·
            refine ⟨2515954657798690200004495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3354606210398253600005993 2515954657798690200004495)
            ·
              refine ⟨3773931986698035300006743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2515954657798690200004495 3773931986698035300006743)
              ·
                refine ⟨5660897980047052950010115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3773931986698035300006743 5660897980047052950010115)
                ·
                  refine ⟨8491346970070579425015173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5660897980047052950010115 8491346970070579425015173)
                  ·
                    refine ⟨1592127556888233642190345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8491346970070579425015173 1592127556888233642190345)
                    ·
                      refine ⟨1194095667666175231642759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1592127556888233642190345 1194095667666175231642759)
                      ·
                        rfl

theorem cell23_2325493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_2325493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325493 prefixEnd_2325493 := by exact prefixLift 2325493
  have htrace : WordTrace (prefixWord ++ tailWord_2325493) baseStart_2325493 baseEnd_2325493 := by
    simpa [prefixWord, tailWord_2325493, baseEnd_2325493] using wordTrace_append hprefix tailTrace_2325493
  have hstable : (prefixWord ++ tailWord_2325493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325493).length < 2 ^ (prefixWord ++ tailWord_2325493).sum := by decide
  have hdescent : baseEnd_2325493 < baseStart_2325493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325515 : List Nat := [1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 4]
def baseStart_2325515 : Nat := 118140960795 + 2325515 * 2 ^ 59
def prefixEnd_2325515 : Nat := 4983230072969 + 3 ^ 40 * 2325515 * 2
def baseEnd_2325515 : Nat := 1194106964240574145567657

theorem tailTrace_2325515 : CollatzResearch.WordTrace tailWord_2325515 prefixEnd_2325515 1194106964240574145567657 := by
  unfold tailWord_2325515
  simp only [CollatzResearch.WordTrace]
  refine ⟨84818500170063796187081999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56545666780042530791387999 84818500170063796187081999)
  ·
    refine ⟨127227750255095694280622999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84818500170063796187081999 127227750255095694280622999)
    ·
      refine ⟨190841625382643541420934499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127227750255095694280622999 190841625382643541420934499)
      ·
        refine ⟨286262438073965312131401749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190841625382643541420934499 286262438073965312131401749)
        ·
          refine ⟨13418551784717124006159457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 286262438073965312131401749 13418551784717124006159457)
          ·
            refine ⟨10063913838537843004619593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13418551784717124006159457 10063913838537843004619593)
            ·
              refine ⟨7547935378903382253464695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10063913838537843004619593 7547935378903382253464695)
              ·
                refine ⟨11321903068355073380197043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7547935378903382253464695 11321903068355073380197043)
                ·
                  refine ⟨16982854602532610070295565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11321903068355073380197043 16982854602532610070295565)
                  ·
                    refine ⟨6368570475949728776360837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16982854602532610070295565 6368570475949728776360837)
                    ·
                      refine ⟨1194106964240574145567657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6368570475949728776360837 1194106964240574145567657)
                      ·
                        rfl

theorem cell23_2325515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 4].length) (baseStart_2325515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325515 prefixEnd_2325515 := by exact prefixLift 2325515
  have htrace : WordTrace (prefixWord ++ tailWord_2325515) baseStart_2325515 baseEnd_2325515 := by
    simpa [prefixWord, tailWord_2325515, baseEnd_2325515] using wordTrace_append hprefix tailTrace_2325515
  have hstable : (prefixWord ++ tailWord_2325515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325515).length < 2 ^ (prefixWord ++ tailWord_2325515).sum := by decide
  have hdescent : baseEnd_2325515 < baseStart_2325515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325633 : List Nat := [1, 2, 4, 2, 2, 2, 2, 3, 1, 1, 3]
def baseStart_2325633 : Nat := 118140960795 + 2325633 * 2 ^ 59
def prefixEnd_2325633 : Nat := 4983230072969 + 3 ^ 40 * 2325633 * 2
def baseEnd_2325633 : Nat := 1194167554957804683892115

theorem tailTrace_2325633 : CollatzResearch.WordTrace tailWord_2325633 prefixEnd_2325633 1194167554957804683892115 := by
  unfold tailWord_2325633
  simp only [CollatzResearch.WordTrace]
  refine ⟨84822803983636302339877553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56548535989090868226585035 84822803983636302339877553)
  ·
    refine ⟨63617102987727226754908165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84822803983636302339877553 63617102987727226754908165)
    ·
      refine ⟨11928206810198855016545281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63617102987727226754908165 11928206810198855016545281)
      ·
        refine ⟨8946155107649141262408961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11928206810198855016545281 8946155107649141262408961)
        ·
          refine ⟨6709616330736855946806721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8946155107649141262408961 6709616330736855946806721)
          ·
            refine ⟨5032212248052641960105041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6709616330736855946806721 5032212248052641960105041)
            ·
              refine ⟨3774159186039481470078781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5032212248052641960105041 3774159186039481470078781)
              ·
                refine ⟨1415309694764805551279543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3774159186039481470078781 1415309694764805551279543)
                ·
                  refine ⟨2122964542147208326919315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1415309694764805551279543 2122964542147208326919315)
                  ·
                    refine ⟨3184446813220812490378973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2122964542147208326919315 3184446813220812490378973)
                    ·
                      refine ⟨1194167554957804683892115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3184446813220812490378973 1194167554957804683892115)
                      ·
                        rfl

theorem cell23_2325633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_2325633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325633 prefixEnd_2325633 := by exact prefixLift 2325633
  have htrace : WordTrace (prefixWord ++ tailWord_2325633) baseStart_2325633 baseEnd_2325633 := by
    simpa [prefixWord, tailWord_2325633, baseEnd_2325633] using wordTrace_append hprefix tailTrace_2325633
  have hstable : (prefixWord ++ tailWord_2325633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325633).length < 2 ^ (prefixWord ++ tailWord_2325633).sum := by decide
  have hdescent : baseEnd_2325633 < baseStart_2325633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325636 : List Nat := [2, 3, 2, 1, 2, 4, 2, 1, 1, 5]
def baseStart_2325636 : Nat := 118140960795 + 2325636 * 2 ^ 59
def prefixEnd_2325636 : Nat := 4983230072969 + 3 ^ 40 * 2325636 * 2
def baseEnd_2325636 : Nat := 398056365133256057384867

theorem tailTrace_2325636 : CollatzResearch.WordTrace tailWord_2325636 prefixEnd_2325636 398056365133256057384867 := by
  unfold tailWord_2325636
  simp only [CollatzResearch.WordTrace]
  refine ⟨42411456701312716926118381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56548608935083622568157841 42411456701312716926118381)
  ·
    refine ⟨15904296262992268847294393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42411456701312716926118381 15904296262992268847294393)
    ·
      refine ⟨11928222197244201635470795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15904296262992268847294393 11928222197244201635470795)
      ·
        refine ⟨17892333295866302453206193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11928222197244201635470795 17892333295866302453206193)
        ·
          refine ⟨13419249971899726839904645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17892333295866302453206193 13419249971899726839904645)
          ·
            refine ⟨2516109369731198782482121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13419249971899726839904645 2516109369731198782482121)
            ·
              refine ⟨1887082027298399086861591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2516109369731198782482121 1887082027298399086861591)
              ·
                refine ⟨2830623040947598630292387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1887082027298399086861591 2830623040947598630292387)
                ·
                  refine ⟨4245934561421397945438581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2830623040947598630292387 4245934561421397945438581)
                  ·
                    refine ⟨398056365133256057384867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4245934561421397945438581 398056365133256057384867)
                    ·
                      rfl

theorem cell23_2325636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_2325636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325636 prefixEnd_2325636 := by exact prefixLift 2325636
  have htrace : WordTrace (prefixWord ++ tailWord_2325636) baseStart_2325636 baseEnd_2325636 := by
    simpa [prefixWord, tailWord_2325636, baseEnd_2325636] using wordTrace_append hprefix tailTrace_2325636
  have hstable : (prefixWord ++ tailWord_2325636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325636).length < 2 ^ (prefixWord ++ tailWord_2325636).sum := by decide
  have hdescent : baseEnd_2325636 < baseStart_2325636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325639 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 7, 2, 2]
def baseStart_2325639 : Nat := 118140960795 + 2325639 * 2 ^ 59
def prefixEnd_2325639 : Nat := 4983230072969 + 3 ^ 40 * 2325639 * 2
def baseEnd_2325639 : Nat := 1194170635841731660417087

theorem tailTrace_2325639 : CollatzResearch.WordTrace tailWord_2325639 prefixEnd_2325639 1194170635841731660417087 := by
  unfold tailWord_2325639
  simp only [CollatzResearch.WordTrace]
  refine ⟨84823022821614565364595971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56548681881076376909730647 84823022821614565364595971)
  ·
    refine ⟨127234534232421848046893957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84823022821614565364595971 127234534232421848046893957)
    ·
      refine ⟨23856475168579096508792617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127234534232421848046893957 23856475168579096508792617)
      ·
        refine ⟨17892356376434322381594463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23856475168579096508792617 17892356376434322381594463)
        ·
          refine ⟨26838534564651483572391695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17892356376434322381594463 26838534564651483572391695)
          ·
            refine ⟨40257801846977225358587543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26838534564651483572391695 40257801846977225358587543)
            ·
              refine ⟨60386702770465838037881315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40257801846977225358587543 60386702770465838037881315)
              ·
                refine ⟨90580054155698757056821973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60386702770465838037881315 90580054155698757056821973)
                ·
                  refine ⟨2122970019274189618519265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 90580054155698757056821973 2122970019274189618519265)
                  ·
                    refine ⟨1592227514455642213889449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2122970019274189618519265 1592227514455642213889449)
                    ·
                      refine ⟨1194170635841731660417087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1592227514455642213889449 1194170635841731660417087)
                      ·
                        rfl

theorem cell23_2325639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_2325639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325639 prefixEnd_2325639 := by exact prefixLift 2325639
  have htrace : WordTrace (prefixWord ++ tailWord_2325639) baseStart_2325639 baseEnd_2325639 := by
    simpa [prefixWord, tailWord_2325639, baseEnd_2325639] using wordTrace_append hprefix tailTrace_2325639
  have hstable : (prefixWord ++ tailWord_2325639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325639).length < 2 ^ (prefixWord ++ tailWord_2325639).sum := by decide
  have hdescent : baseEnd_2325639 < baseStart_2325639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325642 : List Nat := [3, 1, 2, 3, 1, 1, 2, 3, 1, 1, 5]
def baseStart_2325642 : Nat := 118140960795 + 2325642 * 2 ^ 59
def prefixEnd_2325642 : Nat := 4983230072969 + 3 ^ 40 * 2325642 * 2
def baseEnd_2325642 : Nat := 1194172176283695148679573

theorem tailTrace_2325642 : CollatzResearch.WordTrace tailWord_2325642 prefixEnd_2325642 1194172176283695148679573 := by
  unfold tailWord_2325642
  simp only [CollatzResearch.WordTrace]
  refine ⟨21205783060150924219238795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56548754827069131251303453 21205783060150924219238795)
  ·
    refine ⟨31808674590226386328858193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21205783060150924219238795 31808674590226386328858193)
    ·
      refine ⟨23856505942669789746643645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31808674590226386328858193 23856505942669789746643645)
      ·
        refine ⟨8946189728501171154991367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23856505942669789746643645 8946189728501171154991367)
        ·
          refine ⟨13419284592751756732487051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8946189728501171154991367 13419284592751756732487051)
          ·
            refine ⟨20128926889127635098730577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13419284592751756732487051 20128926889127635098730577)
            ·
              refine ⟨15096695166845726324047933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20128926889127635098730577 15096695166845726324047933)
              ·
                refine ⟨5661260687567147371517975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15096695166845726324047933 5661260687567147371517975)
                ·
                  refine ⟨8491891031350721057276963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5661260687567147371517975 8491891031350721057276963)
                  ·
                    refine ⟨12737836547026081585915445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8491891031350721057276963 12737836547026081585915445)
                    ·
                      refine ⟨1194172176283695148679573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12737836547026081585915445 1194172176283695148679573)
                      ·
                        rfl

theorem cell23_2325642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_2325642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325642 prefixEnd_2325642 := by exact prefixLift 2325642
  have htrace : WordTrace (prefixWord ++ tailWord_2325642) baseStart_2325642 baseEnd_2325642 := by
    simpa [prefixWord, tailWord_2325642, baseEnd_2325642] using wordTrace_append hprefix tailTrace_2325642
  have hstable : (prefixWord ++ tailWord_2325642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325642).length < 2 ^ (prefixWord ++ tailWord_2325642).sum := by decide
  have hdescent : baseEnd_2325642 < baseStart_2325642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325656 : List Nat := [2, 1, 2, 4, 2, 1, 1, 3, 3, 2, 2]
def baseStart_2325656 : Nat := 118140960795 + 2325656 * 2 ^ 59
def prefixEnd_2325656 : Nat := 4983230072969 + 3 ^ 40 * 2325656 * 2
def baseEnd_2325656 : Nat := 1194179365012858093904509

theorem tailTrace_2325656 : CollatzResearch.WordTrace tailWord_2325656 prefixEnd_2325656 1194179365012858093904509 := by
  unfold tailWord_2325656
  simp only [CollatzResearch.WordTrace]
  refine ⟨42411821431276488633982411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56549095241701984845309881 42411821431276488633982411)
  ·
    refine ⟨63617732146914732950973617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42411821431276488633982411 63617732146914732950973617)
    ·
      refine ⟨47713299110186049713230213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63617732146914732950973617 47713299110186049713230213)
      ·
        refine ⟨8946243583159884321230665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47713299110186049713230213 8946243583159884321230665)
        ·
          refine ⟨6709682687369913240922999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8946243583159884321230665 6709682687369913240922999)
          ·
            refine ⟨10064524031054869861384499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6709682687369913240922999 10064524031054869861384499)
            ·
              refine ⟨15096786046582304792076749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10064524031054869861384499 15096786046582304792076749)
              ·
                refine ⟨5661294767468364297028781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15096786046582304792076749 5661294767468364297028781)
                ·
                  refine ⟨2122985537800636611385793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5661294767468364297028781 2122985537800636611385793)
                  ·
                    refine ⟨1592239153350477458539345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2122985537800636611385793 1592239153350477458539345)
                    ·
                      refine ⟨1194179365012858093904509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1592239153350477458539345 1194179365012858093904509)
                      ·
                        rfl

theorem cell23_2325656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_2325656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325656 prefixEnd_2325656 := by exact prefixLift 2325656
  have htrace : WordTrace (prefixWord ++ tailWord_2325656) baseStart_2325656 baseEnd_2325656 := by
    simpa [prefixWord, tailWord_2325656, baseEnd_2325656] using wordTrace_append hprefix tailTrace_2325656
  have hstable : (prefixWord ++ tailWord_2325656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325656).length < 2 ^ (prefixWord ++ tailWord_2325656).sum := by decide
  have hdescent : baseEnd_2325656 < baseStart_2325656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325666 : List Nat := [3, 3, 1, 3, 2, 2, 1, 1, 1, 6]
def baseStart_2325666 : Nat := 118140960795 + 2325666 * 2 ^ 59
def prefixEnd_2325666 : Nat := 4983230072969 + 3 ^ 40 * 2325666 * 2
def baseEnd_2325666 : Nat := 398061499939801018259821

theorem tailTrace_2325666 : CollatzResearch.WordTrace tailWord_2325666 prefixEnd_2325666 398061499939801018259821 := by
  unfold tailWord_2325666
  simp only [CollatzResearch.WordTrace]
  refine ⟨21206001898129187243957213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56549338395011165983885901 21206001898129187243957213)
  ·
    refine ⟨7952250711798445216483955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21206001898129187243957213 7952250711798445216483955)
    ·
      refine ⟨11928376067697667824725933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7952250711798445216483955 11928376067697667824725933)
      ·
        refine ⟨4473141025386625434272225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11928376067697667824725933 4473141025386625434272225)
        ·
          refine ⟨3354855769039969075704169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4473141025386625434272225 3354855769039969075704169)
          ·
            refine ⟨2516141826779976806778127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3354855769039969075704169 2516141826779976806778127)
            ·
              refine ⟨3774212740169965210167191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2516141826779976806778127 3774212740169965210167191)
              ·
                refine ⟨5661319110254947815250787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3774212740169965210167191 5661319110254947815250787)
                ·
                  refine ⟨8491978665382421722876181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5661319110254947815250787 8491978665382421722876181)
                  ·
                    refine ⟨398061499939801018259821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8491978665382421722876181 398061499939801018259821)
                    ·
                      rfl

theorem cell23_2325666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_2325666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325666 prefixEnd_2325666 := by exact prefixLift 2325666
  have htrace : WordTrace (prefixWord ++ tailWord_2325666) baseStart_2325666 baseEnd_2325666 := by
    simpa [prefixWord, tailWord_2325666, baseEnd_2325666] using wordTrace_append hprefix tailTrace_2325666
  have hstable : (prefixWord ++ tailWord_2325666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325666).length < 2 ^ (prefixWord ++ tailWord_2325666).sum := by decide
  have hdescent : baseEnd_2325666 < baseStart_2325666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325669 : List Nat := [1, 3, 1, 2, 1, 6, 1, 1, 1, 2, 4]
def baseStart_2325669 : Nat := 118140960795 + 2325669 * 2 ^ 59
def prefixEnd_2325669 : Nat := 4983230072969 + 3 ^ 40 * 2325669 * 2
def baseEnd_2325669 : Nat := 1194186040261366543041949

theorem tailTrace_2325669 : CollatzResearch.WordTrace tailWord_2325669 prefixEnd_2325669 1194186040261366543041949 := by
  unfold tailWord_2325669
  simp only [CollatzResearch.WordTrace]
  refine ⟨84824117011505880488188061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56549411341003920325458707 84824117011505880488188061)
  ·
    refine ⟨31809043879314705183070523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84824117011505880488188061 31809043879314705183070523)
    ·
      refine ⟨47713565818972057774605785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31809043879314705183070523 47713565818972057774605785)
      ·
        refine ⟨35785174364229043330954339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47713565818972057774605785 35785174364229043330954339)
        ·
          refine ⟨53677761546343564996431509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35785174364229043330954339 53677761546343564996431509)
          ·
            refine ⟨2516145072484854609207727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 53677761546343564996431509 2516145072484854609207727)
            ·
              refine ⟨3774217608727281913811591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2516145072484854609207727 3774217608727281913811591)
              ·
                refine ⟨5661326413090922870717387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3774217608727281913811591 5661326413090922870717387)
                ·
                  refine ⟨8491989619636384306076081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5661326413090922870717387 8491989619636384306076081)
                  ·
                    refine ⟨6368992214727288229557061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8491989619636384306076081 6368992214727288229557061)
                    ·
                      refine ⟨1194186040261366543041949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6368992214727288229557061 1194186040261366543041949)
                      ·
                        rfl

theorem cell23_2325669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_2325669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325669 prefixEnd_2325669 := by exact prefixLift 2325669
  have htrace : WordTrace (prefixWord ++ tailWord_2325669) baseStart_2325669 baseEnd_2325669 := by
    simpa [prefixWord, tailWord_2325669, baseEnd_2325669] using wordTrace_append hprefix tailTrace_2325669
  have hstable : (prefixWord ++ tailWord_2325669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325669).length < 2 ^ (prefixWord ++ tailWord_2325669).sum := by decide
  have hdescent : baseEnd_2325669 < baseStart_2325669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325689 : List Nat := [1, 2, 1, 4, 1, 3, 1, 2, 4, 1, 3]
def baseStart_2325689 : Nat := 118140960795 + 2325689 * 2 ^ 59
def prefixEnd_2325689 : Nat := 4983230072969 + 3 ^ 40 * 2325689 * 2
def baseEnd_2325689 : Nat := 1194196309874456464791857

theorem tailTrace_2325689 : CollatzResearch.WordTrace tailWord_2325689 prefixEnd_2325689 1194196309874456464791857 := by
  unfold tailWord_2325689
  simp only [CollatzResearch.WordTrace]
  refine ⟨84824846471433423903916121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56549897647622282602610747 84824846471433423903916121)
  ·
    refine ⟨63618634853575067927937091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84824846471433423903916121 63618634853575067927937091)
    ·
      refine ⟨95427952280362601891905637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63618634853575067927937091 95427952280362601891905637)
      ·
        refine ⟨17892741052567987854732307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95427952280362601891905637 17892741052567987854732307)
        ·
          refine ⟨26839111578851981782098461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17892741052567987854732307 26839111578851981782098461)
          ·
            refine ⟨10064666842069493168286923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26839111578851981782098461 10064666842069493168286923)
            ·
              refine ⟨15097000263104239752430385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10064666842069493168286923 15097000263104239752430385)
              ·
                refine ⟨11322750197328179814322789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15097000263104239752430385 11322750197328179814322789)
                ·
                  refine ⟨2123015661999033715185523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11322750197328179814322789 2123015661999033715185523)
                  ·
                    refine ⟨3184523492998550572778285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2123015661999033715185523 3184523492998550572778285)
                    ·
                      refine ⟨1194196309874456464791857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3184523492998550572778285 1194196309874456464791857)
                      ·
                        rfl

theorem cell23_2325689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_2325689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325689 prefixEnd_2325689 := by exact prefixLift 2325689
  have htrace : WordTrace (prefixWord ++ tailWord_2325689) baseStart_2325689 baseEnd_2325689 := by
    simpa [prefixWord, tailWord_2325689, baseEnd_2325689] using wordTrace_append hprefix tailTrace_2325689
  have hstable : (prefixWord ++ tailWord_2325689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325689).length < 2 ^ (prefixWord ++ tailWord_2325689).sum := by decide
  have hdescent : baseEnd_2325689 < baseStart_2325689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325732 : List Nat := [2, 3, 1, 1, 1, 2, 3, 2, 2, 1, 5]
def baseStart_2325732 : Nat := 118140960795 + 2325732 * 2 ^ 59
def prefixEnd_2325732 : Nat := 4983230072969 + 3 ^ 40 * 2325732 * 2
def baseEnd_2325732 : Nat := 1194218389542599796554159

theorem tailTrace_2325732 : CollatzResearch.WordTrace tailWord_2325732 prefixEnd_2325732 1194218389542599796554159 := by
  unfold tailWord_2325732
  simp only [CollatzResearch.WordTrace]
  refine ⟨42413207405138821123865725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56550943206851761498487633 42413207405138821123865725)
  ·
    refine ⟨15904952776927057921449647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42413207405138821123865725 15904952776927057921449647)
    ·
      refine ⟨23857429165390586882174471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15904952776927057921449647 23857429165390586882174471)
      ·
        refine ⟨35786143748085880323261707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23857429165390586882174471 35786143748085880323261707)
        ·
          refine ⟨53679215622128820484892561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35786143748085880323261707 53679215622128820484892561)
          ·
            refine ⟨40259411716596615363669421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53679215622128820484892561 40259411716596615363669421)
            ·
              refine ⟨15097279393723730761376033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40259411716596615363669421 15097279393723730761376033)
              ·
                refine ⟨11322959545292798071032025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15097279393723730761376033 11322959545292798071032025)
                ·
                  refine ⟨8492219658969598553274019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11322959545292798071032025 8492219658969598553274019)
                  ·
                    refine ⟨12738329488454397829911029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8492219658969598553274019 12738329488454397829911029)
                    ·
                      refine ⟨1194218389542599796554159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12738329488454397829911029 1194218389542599796554159)
                      ·
                        rfl

theorem cell23_2325732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_2325732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325732 prefixEnd_2325732 := by exact prefixLift 2325732
  have htrace : WordTrace (prefixWord ++ tailWord_2325732) baseStart_2325732 baseEnd_2325732 := by
    simpa [prefixWord, tailWord_2325732, baseEnd_2325732] using wordTrace_append hprefix tailTrace_2325732
  have hstable : (prefixWord ++ tailWord_2325732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325732).length < 2 ^ (prefixWord ++ tailWord_2325732).sum := by decide
  have hdescent : baseEnd_2325732 < baseStart_2325732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325763 : List Nat := [1, 1, 1, 3, 2, 5, 2, 2, 2, 2, 2]
def baseStart_2325763 : Nat := 118140960795 + 2325763 * 2 ^ 59
def prefixEnd_2325763 : Nat := 4983230072969 + 3 ^ 40 * 2325763 * 2
def baseEnd_2325763 : Nat := 1194234307442889175266517

theorem tailTrace_2325763 : CollatzResearch.WordTrace tailWord_2325763 prefixEnd_2325763 1194234307442889175266517 := by
  unfold tailWord_2325763
  simp only [CollatzResearch.WordTrace]
  refine ⟨84827545473165334542109943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56551696982110223028073295 84827545473165334542109943)
  ·
    refine ⟨127241318209748001813164915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84827545473165334542109943 127241318209748001813164915)
    ·
      refine ⟨190861977314622002719747373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127241318209748001813164915 190861977314622002719747373)
      ·
        refine ⟨71573241492983251019905265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190861977314622002719747373 71573241492983251019905265)
        ·
          refine ⟨53679931119737438264928949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71573241492983251019905265 53679931119737438264928949)
          ·
            refine ⟨5032493542475384837337089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53679931119737438264928949 5032493542475384837337089)
            ·
              refine ⟨3774370156856538628002817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5032493542475384837337089 3774370156856538628002817)
              ·
                refine ⟨2830777617642403971002113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3774370156856538628002817 2830777617642403971002113)
                ·
                  refine ⟨2123083213231802978251585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2830777617642403971002113 2123083213231802978251585)
                  ·
                    refine ⟨1592312409923852233688689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2123083213231802978251585 1592312409923852233688689)
                    ·
                      refine ⟨1194234307442889175266517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1592312409923852233688689 1194234307442889175266517)
                      ·
                        rfl

theorem cell23_2325763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 2, 2, 2].length) (baseStart_2325763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325763 prefixEnd_2325763 := by exact prefixLift 2325763
  have htrace : WordTrace (prefixWord ++ tailWord_2325763) baseStart_2325763 baseEnd_2325763 := by
    simpa [prefixWord, tailWord_2325763, baseEnd_2325763] using wordTrace_append hprefix tailTrace_2325763
  have hstable : (prefixWord ++ tailWord_2325763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325763).length < 2 ^ (prefixWord ++ tailWord_2325763).sum := by decide
  have hdescent : baseEnd_2325763 < baseStart_2325763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325769 : List Nat := [1, 2, 1, 1, 3, 3, 3, 4, 5]
def baseStart_2325769 : Nat := 118140960795 + 2325769 * 2 ^ 59
def prefixEnd_2325769 : Nat := 4983230072969 + 3 ^ 40 * 2325769 * 2
def baseEnd_2325769 : Nat := 132693043147424016865721

theorem tailTrace_2325769 : CollatzResearch.WordTrace tailWord_2325769 prefixEnd_2325769 132693043147424016865721 := by
  unfold tailWord_2325769
  simp only [CollatzResearch.WordTrace]
  refine ⟨84827764311143597566828361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56551842874095731711218907 84827764311143597566828361)
  ·
    refine ⟨63620823233357698175121271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84827764311143597566828361 63620823233357698175121271)
    ·
      refine ⟨95431234850036547262681907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63620823233357698175121271 95431234850036547262681907)
      ·
        refine ⟨143146852275054820894022861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95431234850036547262681907 143146852275054820894022861)
        ·
          refine ⟨53680069603145557835258573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143146852275054820894022861 53680069603145557835258573)
          ·
            refine ⟨20130026101179584188221965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53680069603145557835258573 20130026101179584188221965)
            ·
              refine ⟨7548759787942344070583237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20130026101179584188221965 7548759787942344070583237)
              ·
                refine ⟨1415392460239189513234357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7548759787942344070583237 1415392460239189513234357)
                ·
                  refine ⟨132693043147424016865721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1415392460239189513234357 132693043147424016865721)
                  ·
                    rfl

theorem cell23_2325769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 4, 5].length) (baseStart_2325769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325769 prefixEnd_2325769 := by exact prefixLift 2325769
  have htrace : WordTrace (prefixWord ++ tailWord_2325769) baseStart_2325769 baseEnd_2325769 := by
    simpa [prefixWord, tailWord_2325769, baseEnd_2325769] using wordTrace_append hprefix tailTrace_2325769
  have hstable : (prefixWord ++ tailWord_2325769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325769).length < 2 ^ (prefixWord ++ tailWord_2325769).sum := by decide
  have hdescent : baseEnd_2325769 < baseStart_2325769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325814 : List Nat := [5, 1, 2, 3, 1, 2, 1, 2, 2, 2, 2]
def baseStart_2325814 : Nat := 118140960795 + 2325814 * 2 ^ 59
def prefixEnd_2325814 : Nat := 4983230072969 + 3 ^ 40 * 2325814 * 2
def baseEnd_2325814 : Nat := 1194260494956268475728783

theorem tailTrace_2325814 : CollatzResearch.WordTrace tailWord_2325814 prefixEnd_2325814 1194260494956268475728783 := by
  unfold tailWord_2325814
  simp only [CollatzResearch.WordTrace]
  refine ⟨5301837849748785640763531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56552937063987046834810997 5301837849748785640763531)
  ·
    refine ⟨7952756774623178461145297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5301837849748785640763531 7952756774623178461145297)
    ·
      refine ⟨5964567580967383845858973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7952756774623178461145297 5964567580967383845858973)
      ·
        refine ⟨2236712842862768942197115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5964567580967383845858973 2236712842862768942197115)
        ·
          refine ⟨3355069264294153413295673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2236712842862768942197115 3355069264294153413295673)
          ·
            refine ⟨2516301948220615059971755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3355069264294153413295673 2516301948220615059971755)
            ·
              refine ⟨3774452922330922589957633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2516301948220615059971755 3774452922330922589957633)
              ·
                refine ⟨2830839691748191942468225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3774452922330922589957633 2830839691748191942468225)
                ·
                  refine ⟨2123129768811143956851169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2830839691748191942468225 2123129768811143956851169)
                  ·
                    refine ⟨1592347326608357967638377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2123129768811143956851169 1592347326608357967638377)
                    ·
                      refine ⟨1194260494956268475728783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1592347326608357967638377 1194260494956268475728783)
                      ·
                        rfl

theorem cell23_2325814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_2325814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325814 prefixEnd_2325814 := by exact prefixLift 2325814
  have htrace : WordTrace (prefixWord ++ tailWord_2325814) baseStart_2325814 baseEnd_2325814 := by
    simpa [prefixWord, tailWord_2325814, baseEnd_2325814] using wordTrace_append hprefix tailTrace_2325814
  have hstable : (prefixWord ++ tailWord_2325814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325814).length < 2 ^ (prefixWord ++ tailWord_2325814).sum := by decide
  have hdescent : baseEnd_2325814 < baseStart_2325814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325832 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 4, 1, 6]
def baseStart_2325832 : Nat := 118140960795 + 2325832 * 2 ^ 59
def prefixEnd_2325832 : Nat := 4983230072969 + 3 ^ 40 * 2325832 * 2
def baseEnd_2325832 : Nat := 1194269737608049405303699

theorem tailTrace_2325832 : CollatzResearch.WordTrace tailWord_2325832 prefixEnd_2325832 1194269737608049405303699 := by
  unfold tailWord_2325832
  simp only [CollatzResearch.WordTrace]
  refine ⟨42415031054957679663185875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56553374739943572884247833 42415031054957679663185875)
  ·
    refine ⟨63622546582436519494778813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42415031054957679663185875 63622546582436519494778813)
    ·
      refine ⟨23858454968413694810542055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63622546582436519494778813 23858454968413694810542055)
      ·
        refine ⟨35787682452620542215813083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23858454968413694810542055 35787682452620542215813083)
        ·
          refine ⟨53681523678930813323719625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35787682452620542215813083 53681523678930813323719625)
          ·
            refine ⟨40261142759198109992789719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53681523678930813323719625 40261142759198109992789719)
            ·
              refine ⟨60391714138797164989184579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40261142759198109992789719 60391714138797164989184579)
              ·
                refine ⟨90587571208195747483776869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60391714138797164989184579 90587571208195747483776869)
                ·
                  refine ⟨16985169601536702653208163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90587571208195747483776869 16985169601536702653208163)
                  ·
                    refine ⟨25477754402305053979812245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16985169601536702653208163 25477754402305053979812245)
                    ·
                      refine ⟨1194269737608049405303699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25477754402305053979812245 1194269737608049405303699)
                      ·
                        rfl

theorem cell23_2325832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_2325832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325832 prefixEnd_2325832 := by exact prefixLift 2325832
  have htrace : WordTrace (prefixWord ++ tailWord_2325832) baseStart_2325832 baseEnd_2325832 := by
    simpa [prefixWord, tailWord_2325832, baseEnd_2325832] using wordTrace_append hprefix tailTrace_2325832
  have hstable : (prefixWord ++ tailWord_2325832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325832).length < 2 ^ (prefixWord ++ tailWord_2325832).sum := by decide
  have hdescent : baseEnd_2325832 < baseStart_2325832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325836 : List Nat := [2, 2, 1, 3, 2, 2, 2, 1, 2, 4, 2]
def baseStart_2325836 : Nat := 118140960795 + 2325836 * 2 ^ 59
def prefixEnd_2325836 : Nat := 4983230072969 + 3 ^ 40 * 2325836 * 2
def baseEnd_2325836 : Nat := 1194271791530667389653681

theorem tailTrace_2325836 : CollatzResearch.WordTrace tailWord_2325836 prefixEnd_2325836 1194271791530667389653681 := by
  unfold tailWord_2325836
  simp only [CollatzResearch.WordTrace]
  refine ⟨42415104000950434004758681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56553472001267245339678241 42415104000950434004758681)
  ·
    refine ⟨31811328000712825503569011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42415104000950434004758681 31811328000712825503569011)
    ·
      refine ⟨47716992001069238255353517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31811328000712825503569011 47716992001069238255353517)
      ·
        refine ⟨17893872000400964345757569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47716992001069238255353517 17893872000400964345757569)
        ·
          refine ⟨13420404000300723259318177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17893872000400964345757569 13420404000300723259318177)
          ·
            refine ⟨10065303000225542444488633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13420404000300723259318177 10065303000225542444488633)
            ·
              refine ⟨7548977250169156833366475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10065303000225542444488633 7548977250169156833366475)
              ·
                refine ⟨11323465875253735250049713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7548977250169156833366475 11323465875253735250049713)
                ·
                  refine ⟨8492599406440301437537285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11323465875253735250049713 8492599406440301437537285)
                  ·
                    refine ⟨1592362388707556519538241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8492599406440301437537285 1592362388707556519538241)
                    ·
                      refine ⟨1194271791530667389653681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1592362388707556519538241 1194271791530667389653681)
                      ·
                        rfl

theorem cell23_2325836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_2325836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325836 prefixEnd_2325836 := by exact prefixLift 2325836
  have htrace : WordTrace (prefixWord ++ tailWord_2325836) baseStart_2325836 baseEnd_2325836 := by
    simpa [prefixWord, tailWord_2325836, baseEnd_2325836] using wordTrace_append hprefix tailTrace_2325836
  have hstable : (prefixWord ++ tailWord_2325836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325836).length < 2 ^ (prefixWord ++ tailWord_2325836).sum := by decide
  have hdescent : baseEnd_2325836 < baseStart_2325836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325913 : List Nat := [1, 2, 1, 2, 1, 6, 2, 1, 2, 3, 2]
def baseStart_2325913 : Nat := 118140960795 + 2325913 * 2 ^ 59
def prefixEnd_2325913 : Nat := 4983230072969 + 3 ^ 40 * 2325913 * 2
def baseEnd_2325913 : Nat := 1194311329541063588390827

theorem tailTrace_2325913 : CollatzResearch.WordTrace tailWord_2325913 prefixEnd_2325913 1194311329541063588390827 := by
  unfold tailWord_2325913
  simp only [CollatzResearch.WordTrace]
  refine ⟨84833016422621910160070393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56555344281747940106713595 84833016422621910160070393)
  ·
    refine ⟨63624762316966432620052795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84833016422621910160070393 63624762316966432620052795)
    ·
      refine ⟨95437143475449648930079193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63624762316966432620052795 95437143475449648930079193)
      ·
        refine ⟨71577857606587236697559395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95437143475449648930079193 71577857606587236697559395)
        ·
          refine ⟨107366786409880855046339093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71577857606587236697559395 107366786409880855046339093)
          ·
            refine ⟨5032818112963165080297145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 107366786409880855046339093 5032818112963165080297145)
            ·
              refine ⟨3774613584722373810222859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5032818112963165080297145 3774613584722373810222859)
              ·
                refine ⟨5661920377083560715334289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3774613584722373810222859 5661920377083560715334289)
                ·
                  refine ⟨4246440282812670536500717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5661920377083560715334289 4246440282812670536500717)
                  ·
                    refine ⟨1592415106054751451187769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4246440282812670536500717 1592415106054751451187769)
                    ·
                      refine ⟨1194311329541063588390827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1592415106054751451187769 1194311329541063588390827)
                      ·
                        rfl

theorem cell23_2325913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 3, 2].length) (baseStart_2325913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325913 prefixEnd_2325913 := by exact prefixLift 2325913
  have htrace : WordTrace (prefixWord ++ tailWord_2325913) baseStart_2325913 baseEnd_2325913 := by
    simpa [prefixWord, tailWord_2325913, baseEnd_2325913] using wordTrace_append hprefix tailTrace_2325913
  have hstable : (prefixWord ++ tailWord_2325913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325913).length < 2 ^ (prefixWord ++ tailWord_2325913).sum := by decide
  have hdescent : baseEnd_2325913 < baseStart_2325913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325919 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 3, 6]
def baseStart_2325919 : Nat := 118140960795 + 2325919 * 2 ^ 59
def prefixEnd_2325919 : Nat := 4983230072969 + 3 ^ 40 * 2325919 * 2
def baseEnd_2325919 : Nat := 398104803474996854971933

theorem tailTrace_2325919 : CollatzResearch.WordTrace tailWord_2325919 prefixEnd_2325919 398104803474996854971933 := by
  unfold tailWord_2325919
  simp only [CollatzResearch.WordTrace]
  refine ⟨84833235260600173184788811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56555490173733448789859207 84833235260600173184788811)
  ·
    refine ⟨127249852890900259777183217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84833235260600173184788811 127249852890900259777183217)
    ·
      refine ⟨95437389668175194832887413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127249852890900259777183217 95437389668175194832887413)
      ·
        refine ⟨8947255281391424515583195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95437389668175194832887413 8947255281391424515583195)
        ·
          refine ⟨13420882922087136773374793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8947255281391424515583195 13420882922087136773374793)
          ·
            refine ⟨10065662191565352580031095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13420882922087136773374793 10065662191565352580031095)
            ·
              refine ⟨15098493287348028870046643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10065662191565352580031095 15098493287348028870046643)
              ·
                refine ⟨22647739931022043305069965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15098493287348028870046643 22647739931022043305069965)
                ·
                  refine ⟨8492902474133266239401237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22647739931022043305069965 8492902474133266239401237)
                  ·
                    refine ⟨398104803474996854971933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8492902474133266239401237 398104803474996854971933)
                    ·
                      rfl

theorem cell23_2325919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 6].length) (baseStart_2325919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325919 prefixEnd_2325919 := by exact prefixLift 2325919
  have htrace : WordTrace (prefixWord ++ tailWord_2325919) baseStart_2325919 baseEnd_2325919 := by
    simpa [prefixWord, tailWord_2325919, baseEnd_2325919] using wordTrace_append hprefix tailTrace_2325919
  have hstable : (prefixWord ++ tailWord_2325919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325919).length < 2 ^ (prefixWord ++ tailWord_2325919).sum := by decide
  have hdescent : baseEnd_2325919 < baseStart_2325919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325943 : List Nat := [1, 1, 3, 1, 3, 2, 2, 3, 3, 2, 2]
def baseStart_2325943 : Nat := 118140960795 + 2325943 * 2 ^ 59
def prefixEnd_2325943 : Nat := 4983230072969 + 3 ^ 40 * 2325943 * 2
def baseEnd_2325943 : Nat := 1194326733960698471015689

theorem tailTrace_2325943 : CollatzResearch.WordTrace tailWord_2325943 prefixEnd_2325943 1194326733960698471015689 := by
  unfold tailWord_2325943
  simp only [CollatzResearch.WordTrace]
  refine ⟨84834110612513225283662483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56556073741675483522441655 84834110612513225283662483)
  ·
    refine ⟨127251165918769837925493725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84834110612513225283662483 127251165918769837925493725)
    ·
      refine ⟨47719187219538689222060147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127251165918769837925493725 47719187219538689222060147)
      ·
        refine ⟨71578780829308033833090221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47719187219538689222060147 71578780829308033833090221)
        ·
          refine ⟨26842042810990512687408833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71578780829308033833090221 26842042810990512687408833)
          ·
            refine ⟨20131532108242884515556625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26842042810990512687408833 20131532108242884515556625)
            ·
              refine ⟨15098649081182163386667469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20131532108242884515556625 15098649081182163386667469)
              ·
                refine ⟨5661993405443311270000301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15098649081182163386667469 5661993405443311270000301)
                ·
                  refine ⟨2123247527041241726250113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5661993405443311270000301 2123247527041241726250113)
                  ·
                    refine ⟨1592435645280931294687585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2123247527041241726250113 1592435645280931294687585)
                    ·
                      refine ⟨1194326733960698471015689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1592435645280931294687585 1194326733960698471015689)
                      ·
                        rfl

theorem cell23_2325943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 3, 2, 2].length) (baseStart_2325943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325943 prefixEnd_2325943 := by exact prefixLift 2325943
  have htrace : WordTrace (prefixWord ++ tailWord_2325943) baseStart_2325943 baseEnd_2325943 := by
    simpa [prefixWord, tailWord_2325943, baseEnd_2325943] using wordTrace_append hprefix tailTrace_2325943
  have hstable : (prefixWord ++ tailWord_2325943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325943).length < 2 ^ (prefixWord ++ tailWord_2325943).sum := by decide
  have hdescent : baseEnd_2325943 < baseStart_2325943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325976 : List Nat := [2, 1, 2, 2, 2, 1, 4, 2, 1, 3, 3]
def baseStart_2325976 : Nat := 118140960795 + 2325976 * 2 ^ 59
def prefixEnd_2325976 : Nat := 4983230072969 + 3 ^ 40 * 2325976 * 2
def baseEnd_2325976 : Nat := 1194343678822296841903037

theorem tailTrace_2325976 : CollatzResearch.WordTrace tailWord_2325976 prefixEnd_2325976 1194343678822296841903037 := by
  unfold tailWord_2325976
  simp only [CollatzResearch.WordTrace]
  refine ⟨42417657110696835959806891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56556876147595781279742521 42417657110696835959806891)
  ·
    refine ⟨63626485666045253939710337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42417657110696835959806891 63626485666045253939710337)
    ·
      refine ⟨47719864249533940454782753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63626485666045253939710337 47719864249533940454782753)
      ·
        refine ⟨35789898187150455341087065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47719864249533940454782753 35789898187150455341087065)
        ·
          refine ⟨26842423640362841505815299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35789898187150455341087065 26842423640362841505815299)
          ·
            refine ⟨40263635460544262258722949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26842423640362841505815299 40263635460544262258722949)
            ·
              refine ⟨7549431648852049173510553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40263635460544262258722949 7549431648852049173510553)
              ·
                refine ⟨5662073736639036880132915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7549431648852049173510553 5662073736639036880132915)
                ·
                  refine ⟨8493110604958555320199373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5662073736639036880132915 8493110604958555320199373)
                  ·
                    refine ⟨3184916476859458245074765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8493110604958555320199373 3184916476859458245074765)
                    ·
                      refine ⟨1194343678822296841903037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3184916476859458245074765 1194343678822296841903037)
                      ·
                        rfl

theorem cell23_2325976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_2325976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325976 prefixEnd_2325976 := by exact prefixLift 2325976
  have htrace : WordTrace (prefixWord ++ tailWord_2325976) baseStart_2325976 baseEnd_2325976 := by
    simpa [prefixWord, tailWord_2325976, baseEnd_2325976] using wordTrace_append hprefix tailTrace_2325976
  have hstable : (prefixWord ++ tailWord_2325976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325976).length < 2 ^ (prefixWord ++ tailWord_2325976).sum := by decide
  have hdescent : baseEnd_2325976 < baseStart_2325976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325977 : List Nat := [1, 2, 1, 2, 4, 3, 2, 3, 1, 2, 2]
def baseStart_2325977 : Nat := 118140960795 + 2325977 * 2 ^ 59
def prefixEnd_2325977 : Nat := 4983230072969 + 3 ^ 40 * 2325977 * 2
def baseEnd_2325977 : Nat := 1194344192302951337990533

theorem tailTrace_2325977 : CollatzResearch.WordTrace tailWord_2325977 prefixEnd_2325977 1194344192302951337990533 := by
  unfold tailWord_2325977
  simp only [CollatzResearch.WordTrace]
  refine ⟨84835350694390049090400185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56556900462926699393600123 84835350694390049090400185)
  ·
    refine ⟨63626513020792536817800139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84835350694390049090400185 63626513020792536817800139)
    ·
      refine ⟨95439769531188805226700209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63626513020792536817800139 95439769531188805226700209)
      ·
        refine ⟨71579827148391603920025157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95439769531188805226700209 71579827148391603920025157)
        ·
          refine ⟨13421217590323425735004717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71579827148391603920025157 13421217590323425735004717)
          ·
            refine ⟨5032956596371284650626769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13421217590323425735004717 5032956596371284650626769)
            ·
              refine ⟨3774717447278463487970077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5032956596371284650626769 3774717447278463487970077)
              ·
                refine ⟨1415519042729423807988779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3774717447278463487970077 1415519042729423807988779)
                ·
                  refine ⟨2123278564094135711983169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1415519042729423807988779 2123278564094135711983169)
                  ·
                    refine ⟨1592458923070601783987377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2123278564094135711983169 1592458923070601783987377)
                    ·
                      refine ⟨1194344192302951337990533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1592458923070601783987377 1194344192302951337990533)
                      ·
                        rfl

theorem cell23_2325977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 3, 1, 2, 2].length) (baseStart_2325977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325977 prefixEnd_2325977 := by exact prefixLift 2325977
  have htrace : WordTrace (prefixWord ++ tailWord_2325977) baseStart_2325977 baseEnd_2325977 := by
    simpa [prefixWord, tailWord_2325977, baseEnd_2325977] using wordTrace_append hprefix tailTrace_2325977
  have hstable : (prefixWord ++ tailWord_2325977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325977).length < 2 ^ (prefixWord ++ tailWord_2325977).sum := by decide
  have hdescent : baseEnd_2325977 < baseStart_2325977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2325999 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 4]
def baseStart_2325999 : Nat := 118140960795 + 2325999 * 2 ^ 59
def prefixEnd_2325999 : Nat := 4983230072969 + 3 ^ 40 * 2325999 * 2
def baseEnd_2325999 : Nat := 1194355488877350251915431

theorem tailTrace_2325999 : CollatzResearch.WordTrace tailWord_2325999 prefixEnd_2325999 1194355488877350251915431 := by
  unfold tailWord_2325999
  simp only [CollatzResearch.WordTrace]
  refine ⟨84836153100310346847701051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56557435400206897898467367 84836153100310346847701051)
  ·
    refine ⟨127254229650465520271551577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84836153100310346847701051 127254229650465520271551577)
    ·
      refine ⟨95440672237849140203663683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127254229650465520271551577 95440672237849140203663683)
      ·
        refine ⟨143161008356773710305495525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95440672237849140203663683 143161008356773710305495525)
        ·
          refine ⟨26842689066895070682280411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143161008356773710305495525 26842689066895070682280411)
          ·
            refine ⟨40264033600342606023420617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26842689066895070682280411 40264033600342606023420617)
            ·
              refine ⟨30198025200256954517565463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40264033600342606023420617 30198025200256954517565463)
              ·
                refine ⟨45297037800385431776348195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30198025200256954517565463 45297037800385431776348195)
                ·
                  refine ⟨67945556700578147664522293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45297037800385431776348195 67945556700578147664522293)
                  ·
                    refine ⟨6369895940679201343548965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67945556700578147664522293 6369895940679201343548965)
                    ·
                      refine ⟨1194355488877350251915431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6369895940679201343548965 1194355488877350251915431)
                      ·
                        rfl

theorem cell23_2325999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 4].length) (baseStart_2325999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2325999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2325999 prefixEnd_2325999 := by exact prefixLift 2325999
  have htrace : WordTrace (prefixWord ++ tailWord_2325999) baseStart_2325999 baseEnd_2325999 := by
    simpa [prefixWord, tailWord_2325999, baseEnd_2325999] using wordTrace_append hprefix tailTrace_2325999
  have hstable : (prefixWord ++ tailWord_2325999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2325999).length < 2 ^ (prefixWord ++ tailWord_2325999).sum := by decide
  have hdescent : baseEnd_2325999 < baseStart_2325999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2325999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326010 : List Nat := [3, 1, 1, 1, 1, 2, 7, 1, 2, 1, 3]
def baseStart_2326010 : Nat := 118140960795 + 2326010 * 2 ^ 59
def prefixEnd_2326010 : Nat := 4983230072969 + 3 ^ 40 * 2326010 * 2
def baseEnd_2326010 : Nat := 1194361137164549708877881

theorem tailTrace_2326010 : CollatzResearch.WordTrace tailWord_2326010 prefixEnd_2326010 1194361137164549708877881 := by
  unfold tailWord_2326010
  simp only [CollatzResearch.WordTrace]
  refine ⟨21209138575817623931587871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56557702868846997150900989 21209138575817623931587871)
  ·
    refine ⟨31813707863726435897381807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21209138575817623931587871 31813707863726435897381807)
    ·
      refine ⟨47720561795589653846072711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31813707863726435897381807 47720561795589653846072711)
      ·
        refine ⟨71580842693384480769109067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47720561795589653846072711 71580842693384480769109067)
        ·
          refine ⟨107371264040076721153663601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71580842693384480769109067 107371264040076721153663601)
          ·
            refine ⟨80528448030057540865247701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107371264040076721153663601 80528448030057540865247701)
            ·
              refine ⟨1887385500704473614029243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 80528448030057540865247701 1887385500704473614029243)
              ·
                refine ⟨2831078251056710421043865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1887385500704473614029243 2831078251056710421043865)
                ·
                  refine ⟨2123308688292532815782899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2831078251056710421043865 2123308688292532815782899)
                  ·
                    refine ⟨3184963032438799223674349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2123308688292532815782899 3184963032438799223674349)
                    ·
                      refine ⟨1194361137164549708877881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3184963032438799223674349 1194361137164549708877881)
                      ·
                        rfl

theorem cell23_2326010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 1, 2, 1, 3].length) (baseStart_2326010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326010 prefixEnd_2326010 := by exact prefixLift 2326010
  have htrace : WordTrace (prefixWord ++ tailWord_2326010) baseStart_2326010 baseEnd_2326010 := by
    simpa [prefixWord, tailWord_2326010, baseEnd_2326010] using wordTrace_append hprefix tailTrace_2326010
  have hstable : (prefixWord ++ tailWord_2326010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326010).length < 2 ^ (prefixWord ++ tailWord_2326010).sum := by decide
  have hdescent : baseEnd_2326010 < baseStart_2326010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326033 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 6, 2, 2]
def baseStart_2326033 : Nat := 118140960795 + 2326033 * 2 ^ 59
def prefixEnd_2326033 : Nat := 4983230072969 + 3 ^ 40 * 2326033 * 2
def baseEnd_2326033 : Nat := 1194372947219603118890275

theorem tailTrace_2326033 : CollatzResearch.WordTrace tailWord_2326033 prefixEnd_2326033 1194372947219603118890275 := by
  unfold tailWord_2326033
  simp only [CollatzResearch.WordTrace]
  refine ⟨84837393182187170654438753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56558262121458113769625835 84837393182187170654438753)
  ·
    refine ⟨63628044886640377990829065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84837393182187170654438753 63628044886640377990829065)
    ·
      refine ⟨47721033664980283493121799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63628044886640377990829065 47721033664980283493121799)
      ·
        refine ⟨71581550497470425239682699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47721033664980283493121799 71581550497470425239682699)
        ·
          refine ⟨107372325746205637859524049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71581550497470425239682699 107372325746205637859524049)
          ·
            refine ⟨80529244309654228394643037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107372325746205637859524049 80529244309654228394643037)
            ·
              refine ⟨30198466616120335647991139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80529244309654228394643037 30198466616120335647991139)
              ·
                refine ⟨45297699924180503471986709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30198466616120335647991139 45297699924180503471986709)
                ·
                  refine ⟨2123329683945961100249377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45297699924180503471986709 2123329683945961100249377)
                  ·
                    refine ⟨1592497262959470825187033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2123329683945961100249377 1592497262959470825187033)
                    ·
                      refine ⟨1194372947219603118890275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1592497262959470825187033 1194372947219603118890275)
                      ·
                        rfl

theorem cell23_2326033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 6, 2, 2].length) (baseStart_2326033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326033 prefixEnd_2326033 := by exact prefixLift 2326033
  have htrace : WordTrace (prefixWord ++ tailWord_2326033) baseStart_2326033 baseEnd_2326033 := by
    simpa [prefixWord, tailWord_2326033, baseEnd_2326033] using wordTrace_append hprefix tailTrace_2326033
  have hstable : (prefixWord ++ tailWord_2326033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326033).length < 2 ^ (prefixWord ++ tailWord_2326033).sum := by decide
  have hdescent : baseEnd_2326033 < baseStart_2326033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326050 : List Nat := [3, 3, 1, 1, 1, 1, 4, 1, 4, 2, 2]
def baseStart_2326050 : Nat := 118140960795 + 2326050 * 2 ^ 59
def prefixEnd_2326050 : Nat := 4983230072969 + 3 ^ 40 * 2326050 * 2
def baseEnd_2326050 : Nat := 1194381676390729552377697

theorem tailTrace_2326050 : CollatzResearch.WordTrace tailWord_2326050 prefixEnd_2326050 1194381676390729552377697 := by
  unfold tailWord_2326050
  simp only [CollatzResearch.WordTrace]
  refine ⟨21209503305781395639451901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56558675482083721705205069 21209503305781395639451901)
  ·
    refine ⟨7953563739668023364794463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21209503305781395639451901 7953563739668023364794463)
    ·
      refine ⟨11930345609502035047191695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7953563739668023364794463 11930345609502035047191695)
      ·
        refine ⟨17895518414253052570787543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11930345609502035047191695 17895518414253052570787543)
        ·
          refine ⟨26843277621379578856181315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17895518414253052570787543 26843277621379578856181315)
          ·
            refine ⟨40264916432069368284271973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26843277621379578856181315 40264916432069368284271973)
            ·
              refine ⟨7549671831013006553300995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40264916432069368284271973 7549671831013006553300995)
              ·
                refine ⟨11324507746519509829951493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7549671831013006553300995 11324507746519509829951493)
                ·
                  refine ⟨2123345202472408093115905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11324507746519509829951493 2123345202472408093115905)
                  ·
                    refine ⟨1592508901854306069836929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2123345202472408093115905 1592508901854306069836929)
                    ·
                      refine ⟨1194381676390729552377697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1592508901854306069836929 1194381676390729552377697)
                      ·
                        rfl

theorem cell23_2326050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_2326050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326050 prefixEnd_2326050 := by exact prefixLift 2326050
  have htrace : WordTrace (prefixWord ++ tailWord_2326050) baseStart_2326050 baseEnd_2326050 := by
    simpa [prefixWord, tailWord_2326050, baseEnd_2326050] using wordTrace_append hprefix tailTrace_2326050
  have hstable : (prefixWord ++ tailWord_2326050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326050).length < 2 ^ (prefixWord ++ tailWord_2326050).sum := by decide
  have hdescent : baseEnd_2326050 < baseStart_2326050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326066 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3]
def baseStart_2326066 : Nat := 118140960795 + 2326066 * 2 ^ 59
def prefixEnd_2326066 : Nat := 4983230072969 + 3 ^ 40 * 2326066 * 2
def baseEnd_2326066 : Nat := 1194389892081201489777623

theorem tailTrace_2326066 : CollatzResearch.WordTrace tailWord_2326066 prefixEnd_2326066 1194389892081201489777623 := by
  unfold tailWord_2326066
  simp only [CollatzResearch.WordTrace]
  refine ⟨21209649197766904322597513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56559064527378411526926701 21209649197766904322597513)
  ·
    refine ⟨15907236898325178241948135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21209649197766904322597513 15907236898325178241948135)
    ·
      refine ⟨23860855347487767362922203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15907236898325178241948135 23860855347487767362922203)
      ·
        refine ⟨35791283021231651044383305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23860855347487767362922203 35791283021231651044383305)
        ·
          refine ⟨26843462265923738283287479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35791283021231651044383305 26843462265923738283287479)
          ·
            refine ⟨40265193398885607424931219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26843462265923738283287479 40265193398885607424931219)
            ·
              refine ⟨60397790098328411137396829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40265193398885607424931219 60397790098328411137396829)
              ·
                refine ⟨22649171286873154176523811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60397790098328411137396829 22649171286873154176523811)
                ·
                  refine ⟨33973756930309731264785717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22649171286873154176523811 33973756930309731264785717)
                  ·
                    refine ⟨3185039712216537306073661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33973756930309731264785717 3185039712216537306073661)
                    ·
                      refine ⟨1194389892081201489777623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3185039712216537306073661 1194389892081201489777623)
                      ·
                        rfl

theorem cell23_2326066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_2326066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326066 prefixEnd_2326066 := by exact prefixLift 2326066
  have htrace : WordTrace (prefixWord ++ tailWord_2326066) baseStart_2326066 baseEnd_2326066 := by
    simpa [prefixWord, tailWord_2326066, baseEnd_2326066] using wordTrace_append hprefix tailTrace_2326066
  have hstable : (prefixWord ++ tailWord_2326066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326066).length < 2 ^ (prefixWord ++ tailWord_2326066).sum := by decide
  have hdescent : baseEnd_2326066 < baseStart_2326066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326067 : List Nat := [1, 1, 1, 2, 4, 3, 4, 1, 2, 2, 2]
def baseStart_2326067 : Nat := 118140960795 + 2326067 * 2 ^ 59
def prefixEnd_2326067 : Nat := 4983230072969 + 3 ^ 40 * 2326067 * 2
def baseEnd_2326067 : Nat := 1194390405561855985865119

theorem tailTrace_2326067 : CollatzResearch.WordTrace tailWord_2326067 prefixEnd_2326067 1194390405561855985865119 := by
  unfold tailWord_2326067
  simp only [CollatzResearch.WordTrace]
  refine ⟨84838633264063994461176455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56559088842709329640784303 84838633264063994461176455)
  ·
    refine ⟨127257949896095991691764683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84838633264063994461176455 127257949896095991691764683)
    ·
      refine ⟨190886924844143987537647025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127257949896095991691764683 190886924844143987537647025)
      ·
        refine ⟨143165193633107990653235269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190886924844143987537647025 143165193633107990653235269)
        ·
          refine ⟨26843473806207748247481613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143165193633107990653235269 26843473806207748247481613)
          ·
            refine ⟨10066302677327905592805605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26843473806207748247481613 10066302677327905592805605)
            ·
              refine ⟨1887431751998982298651051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10066302677327905592805605 1887431751998982298651051)
              ·
                refine ⟨2831147627998473447976577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1887431751998982298651051 2831147627998473447976577)
                ·
                  refine ⟨2123360720998855085982433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2831147627998473447976577 2123360720998855085982433)
                  ·
                    refine ⟨1592520540749141314486825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2123360720998855085982433 1592520540749141314486825)
                    ·
                      refine ⟨1194390405561855985865119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1592520540749141314486825 1194390405561855985865119)
                      ·
                        rfl

theorem cell23_2326067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 2, 2, 2].length) (baseStart_2326067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326067 prefixEnd_2326067 := by exact prefixLift 2326067
  have htrace : WordTrace (prefixWord ++ tailWord_2326067) baseStart_2326067 baseEnd_2326067 := by
    simpa [prefixWord, tailWord_2326067, baseEnd_2326067] using wordTrace_append hprefix tailTrace_2326067
  have hstable : (prefixWord ++ tailWord_2326067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326067).length < 2 ^ (prefixWord ++ tailWord_2326067).sum := by decide
  have hdescent : baseEnd_2326067 < baseStart_2326067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326099 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 3, 10]
def baseStart_2326099 : Nat := 118140960795 + 2326099 * 2 ^ 59
def prefixEnd_2326099 : Nat := 4983230072969 + 3 ^ 40 * 2326099 * 2
def baseEnd_2326099 : Nat := 398135612314266620221657

theorem tailTrace_2326099 : CollatzResearch.WordTrace tailWord_2326099 prefixEnd_2326099 398135612314266620221657 := by
  unfold tailWord_2326099
  simp only [CollatzResearch.WordTrace]
  refine ⟨84839800399948063926341351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56559866933298709284227567 84839800399948063926341351)
  ·
    refine ⟨127259700599922095889512027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84839800399948063926341351 127259700599922095889512027)
    ·
      refine ⟨190889550899883143834268041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127259700599922095889512027 190889550899883143834268041)
      ·
        refine ⟨143167163174912357875701031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190889550899883143834268041 143167163174912357875701031)
        ·
          refine ⟨214750744762368536813551547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143167163174912357875701031 214750744762368536813551547)
          ·
            refine ⟨322126117143552805220327321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214750744762368536813551547 322126117143552805220327321)
            ·
              refine ⟨241594587857664603915245491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 322126117143552805220327321 241594587857664603915245491)
              ·
                refine ⟨362391881786496905872868237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 241594587857664603915245491 362391881786496905872868237)
                ·
                  refine ⟨135896955669936339702325589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 362391881786496905872868237 135896955669936339702325589)
                  ·
                    refine ⟨398135612314266620221657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 135896955669936339702325589 398135612314266620221657)
                    ·
                      rfl

theorem cell23_2326099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 10].length) (baseStart_2326099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326099 prefixEnd_2326099 := by exact prefixLift 2326099
  have htrace : WordTrace (prefixWord ++ tailWord_2326099) baseStart_2326099 baseEnd_2326099 := by
    simpa [prefixWord, tailWord_2326099, baseEnd_2326099] using wordTrace_append hprefix tailTrace_2326099
  have hstable : (prefixWord ++ tailWord_2326099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326099).length < 2 ^ (prefixWord ++ tailWord_2326099).sum := by decide
  have hdescent : baseEnd_2326099 < baseStart_2326099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326180 : List Nat := [2, 3, 1, 2, 2, 3, 3, 1, 6]
def baseStart_2326180 : Nat := 118140960795 + 2326180 * 2 ^ 59
def prefixEnd_2326180 : Nat := 4983230072969 + 3 ^ 40 * 2326180 * 2
def baseEnd_2326180 : Nat := 132716492097312671528011

theorem tailTrace_2326180 : CollatzResearch.WordTrace tailWord_2326180 prefixEnd_2326180 132716492097312671528011 := by
  unfold tailWord_2326180
  simp only [CollatzResearch.WordTrace]
  refine ⟨42421377356327307380019997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56561836475103076506693329 42421377356327307380019997)
  ·
    refine ⟨15908016508622740267507499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42421377356327307380019997 15908016508622740267507499)
    ·
      refine ⟨23862024762934110401261249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15908016508622740267507499 23862024762934110401261249)
      ·
        refine ⟨17896518572200582800945937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23862024762934110401261249 17896518572200582800945937)
        ·
          refine ⟨13422388929150437100709453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17896518572200582800945937 13422388929150437100709453)
          ·
            refine ⟨5033395848431413912766045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13422388929150437100709453 5033395848431413912766045)
            ·
              refine ⟨1887523443161780217287267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5033395848431413912766045 1887523443161780217287267)
              ·
                refine ⟨2831285164742670325930901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1887523443161780217287267 2831285164742670325930901)
                ·
                  refine ⟨132716492097312671528011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2831285164742670325930901 132716492097312671528011)
                  ·
                    rfl

theorem cell23_2326180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 6].length) (baseStart_2326180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326180 prefixEnd_2326180 := by exact prefixLift 2326180
  have htrace : WordTrace (prefixWord ++ tailWord_2326180) baseStart_2326180 baseEnd_2326180 := by
    simpa [prefixWord, tailWord_2326180, baseEnd_2326180] using wordTrace_append hprefix tailTrace_2326180
  have hstable : (prefixWord ++ tailWord_2326180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326180).length < 2 ^ (prefixWord ++ tailWord_2326180).sum := by decide
  have hdescent : baseEnd_2326180 < baseStart_2326180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326213 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 1, 8, 2]
def baseStart_2326213 : Nat := 118140960795 + 2326213 * 2 ^ 59
def prefixEnd_2326213 : Nat := 4983230072969 + 3 ^ 40 * 2326213 * 2
def baseEnd_2326213 : Nat := 1194465373737412414639447

theorem tailTrace_2326213 : CollatzResearch.WordTrace tailWord_2326213 prefixEnd_2326213 1194465373737412414639447 := by
  unfold tailWord_2326213
  simp only [CollatzResearch.WordTrace]
  refine ⟨84843958321535061395991293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56562638881023374263994195 84843958321535061395991293)
  ·
    refine ⟨31816484370575648023496735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84843958321535061395991293 31816484370575648023496735)
    ·
      refine ⟨47724726555863472035245103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31816484370575648023496735 47724726555863472035245103)
      ·
        refine ⟨71587089833795208052867655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47724726555863472035245103 71587089833795208052867655)
        ·
          refine ⟨107380634750692812079301483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71587089833795208052867655 107380634750692812079301483)
          ·
            refine ⟨161070952126039218118952225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107380634750692812079301483 161070952126039218118952225)
            ·
              refine ⟨120803214094529413589214169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161070952126039218118952225 120803214094529413589214169)
              ·
                refine ⟨90602410570897060191910627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120803214094529413589214169 90602410570897060191910627)
                ·
                  refine ⟨135903615856345590287865941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90602410570897060191910627 135903615856345590287865941)
                  ·
                    refine ⟨1592620498316549886185929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 135903615856345590287865941 1592620498316549886185929)
                    ·
                      refine ⟨1194465373737412414639447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1592620498316549886185929 1194465373737412414639447)
                      ·
                        rfl

theorem cell23_2326213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 8, 2].length) (baseStart_2326213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326213 prefixEnd_2326213 := by exact prefixLift 2326213
  have htrace : WordTrace (prefixWord ++ tailWord_2326213) baseStart_2326213 baseEnd_2326213 := by
    simpa [prefixWord, tailWord_2326213, baseEnd_2326213] using wordTrace_append hprefix tailTrace_2326213
  have hstable : (prefixWord ++ tailWord_2326213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326213).length < 2 ^ (prefixWord ++ tailWord_2326213).sum := by decide
  have hdescent : baseEnd_2326213 < baseStart_2326213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326233 : List Nat := [1, 2, 1, 2, 3, 3, 2, 2, 1, 1, 5]
def baseStart_2326233 : Nat := 118140960795 + 2326233 * 2 ^ 59
def prefixEnd_2326233 : Nat := 4983230072969 + 3 ^ 40 * 2326233 * 2
def baseEnd_2326233 : Nat := 1194475643350502336389355

theorem tailTrace_2326233 : CollatzResearch.WordTrace tailWord_2326233 prefixEnd_2326233 1194475643350502336389355 := by
  unfold tailWord_2326233
  simp only [CollatzResearch.WordTrace]
  refine ⟨84844687781462604811719353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56563125187641736541146235 84844687781462604811719353)
  ·
    refine ⟨63633515836096953608789515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84844687781462604811719353 63633515836096953608789515)
    ·
      refine ⟨95450273754145430413184273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63633515836096953608789515 95450273754145430413184273)
      ·
        refine ⟨71587705315609072809888205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95450273754145430413184273 71587705315609072809888205)
        ·
          refine ⟨26845389493353402303708077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71587705315609072809888205 26845389493353402303708077)
          ·
            refine ⟨10067021060007525863890529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26845389493353402303708077 10067021060007525863890529)
            ·
              refine ⟨7550265795005644397917897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10067021060007525863890529 7550265795005644397917897)
              ·
                refine ⟨5662699346254233298438423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7550265795005644397917897 5662699346254233298438423)
                ·
                  refine ⟨8494049019381349947657635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5662699346254233298438423 8494049019381349947657635)
                  ·
                    refine ⟨12741073529072024921486453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8494049019381349947657635 12741073529072024921486453)
                    ·
                      refine ⟨1194475643350502336389355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12741073529072024921486453 1194475643350502336389355)
                      ·
                        rfl

theorem cell23_2326233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 1, 5].length) (baseStart_2326233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326233 prefixEnd_2326233 := by exact prefixLift 2326233
  have htrace : WordTrace (prefixWord ++ tailWord_2326233) baseStart_2326233 baseEnd_2326233 := by
    simpa [prefixWord, tailWord_2326233, baseEnd_2326233] using wordTrace_append hprefix tailTrace_2326233
  have hstable : (prefixWord ++ tailWord_2326233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326233).length < 2 ^ (prefixWord ++ tailWord_2326233).sum := by decide
  have hdescent : baseEnd_2326233 < baseStart_2326233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326247 : List Nat := [1, 1, 5, 4, 1, 1, 1, 1, 3, 1, 4]
def baseStart_2326247 : Nat := 118140960795 + 2326247 * 2 ^ 59
def prefixEnd_2326247 : Nat := 4983230072969 + 3 ^ 40 * 2326247 * 2
def baseEnd_2326247 : Nat := 1194482832079665281614291

theorem tailTrace_2326247 : CollatzResearch.WordTrace tailWord_2326247 prefixEnd_2326247 1194482832079665281614291 := by
  unfold tailWord_2326247
  simp only [CollatzResearch.WordTrace]
  refine ⟨84845198403411885202728995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56563465602274590135152663 84845198403411885202728995)
  ·
    refine ⟨127267797605117827804093493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84845198403411885202728995 127267797605117827804093493)
    ·
      refine ⟨11931356025479796356633765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 127267797605117827804093493 11931356025479796356633765)
      ·
        refine ⟨2237129254777461816868831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11931356025479796356633765 2237129254777461816868831)
        ·
          refine ⟨3355693882166192725303247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2237129254777461816868831 3355693882166192725303247)
          ·
            refine ⟨5033540823249289087954871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3355693882166192725303247 5033540823249289087954871)
            ·
              refine ⟨7550311234873933631932307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5033540823249289087954871 7550311234873933631932307)
              ·
                refine ⟨11325466852310900447898461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7550311234873933631932307 11325466852310900447898461)
                ·
                  refine ⟨4247050069616587667961923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11325466852310900447898461 4247050069616587667961923)
                  ·
                    refine ⟨6370575104424881501942885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4247050069616587667961923 6370575104424881501942885)
                    ·
                      refine ⟨1194482832079665281614291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6370575104424881501942885 1194482832079665281614291)
                      ·
                        rfl

theorem cell23_2326247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_2326247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326247 prefixEnd_2326247 := by exact prefixLift 2326247
  have htrace : WordTrace (prefixWord ++ tailWord_2326247) baseStart_2326247 baseEnd_2326247 := by
    simpa [prefixWord, tailWord_2326247, baseEnd_2326247] using wordTrace_append hprefix tailTrace_2326247
  have hstable : (prefixWord ++ tailWord_2326247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326247).length < 2 ^ (prefixWord ++ tailWord_2326247).sum := by decide
  have hdescent : baseEnd_2326247 < baseStart_2326247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326253 : List Nat := [1, 5, 1, 2, 1, 2, 2, 9]
def baseStart_2326253 : Nat := 118140960795 + 2326253 * 2 ^ 59
def prefixEnd_2326253 : Nat := 4983230072969 + 3 ^ 40 * 2326253 * 2
def baseEnd_2326253 : Nat := 44240218998651565116269

theorem tailTrace_2326253 : CollatzResearch.WordTrace tailWord_2326253 prefixEnd_2326253 44240218998651565116269 := by
  unfold tailWord_2326253
  simp only [CollatzResearch.WordTrace]
  refine ⟨84845417241390148227447413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56563611494260098818298275 84845417241390148227447413)
  ·
    refine ⟨7954257866380326396323195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84845417241390148227447413 7954257866380326396323195)
    ·
      refine ⟨11931386799570489594484793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7954257866380326396323195 11931386799570489594484793)
      ·
        refine ⟨8948540099677867195863595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11931386799570489594484793 8948540099677867195863595)
        ·
          refine ⟨13422810149516800793795393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8948540099677867195863595 13422810149516800793795393)
          ·
            refine ⟨10067107612137600595346545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13422810149516800793795393 10067107612137600595346545)
            ·
              refine ⟨7550330709103200446509909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10067107612137600595346545 7550330709103200446509909)
              ·
                refine ⟨44240218998651565116269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7550330709103200446509909 44240218998651565116269)
                ·
                  rfl

theorem cell23_2326253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 9].length) (baseStart_2326253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326253 prefixEnd_2326253 := by exact prefixLift 2326253
  have htrace : WordTrace (prefixWord ++ tailWord_2326253) baseStart_2326253 baseEnd_2326253 := by
    simpa [prefixWord, tailWord_2326253, baseEnd_2326253] using wordTrace_append hprefix tailTrace_2326253
  have hstable : (prefixWord ++ tailWord_2326253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326253).length < 2 ^ (prefixWord ++ tailWord_2326253).sum := by decide
  have hdescent : baseEnd_2326253 < baseStart_2326253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326263 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 3, 3, 3]
def baseStart_2326263 : Nat := 118140960795 + 2326263 * 2 ^ 59
def prefixEnd_2326263 : Nat := 4983230072969 + 3 ^ 40 * 2326263 * 2
def baseEnd_2326263 : Nat := 1194491047770137219014217

theorem tailTrace_2326263 : CollatzResearch.WordTrace tailWord_2326263 prefixEnd_2326263 1194491047770137219014217 := by
  unfold tailWord_2326263
  simp only [CollatzResearch.WordTrace]
  refine ⟨84845781971353919935311443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56563854647569279956874295 84845781971353919935311443)
  ·
    refine ⟨127268672957030879902967165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84845781971353919935311443 127268672957030879902967165)
    ·
      refine ⟨47725752358886579963612687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127268672957030879902967165 47725752358886579963612687)
      ·
        refine ⟨71588628538329869945419031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47725752358886579963612687 71588628538329869945419031)
        ·
          refine ⟨107382942807494804918128547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71588628538329869945419031 107382942807494804918128547)
          ·
            refine ⟨161074414211242207377192821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107382942807494804918128547 161074414211242207377192821)
            ·
              refine ⟨15100726332303956941611827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 161074414211242207377192821 15100726332303956941611827)
              ·
                refine ⟨22651089498455935412417741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15100726332303956941611827 22651089498455935412417741)
                ·
                  refine ⟨8494158561920975779656653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22651089498455935412417741 8494158561920975779656653)
                  ·
                    refine ⟨3185309460720365917371245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8494158561920975779656653 3185309460720365917371245)
                    ·
                      refine ⟨1194491047770137219014217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3185309460720365917371245 1194491047770137219014217)
                      ·
                        rfl

theorem cell23_2326263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 3, 3].length) (baseStart_2326263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326263 prefixEnd_2326263 := by exact prefixLift 2326263
  have htrace : WordTrace (prefixWord ++ tailWord_2326263) baseStart_2326263 baseEnd_2326263 := by
    simpa [prefixWord, tailWord_2326263, baseEnd_2326263] using wordTrace_append hprefix tailTrace_2326263
  have hstable : (prefixWord ++ tailWord_2326263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326263).length < 2 ^ (prefixWord ++ tailWord_2326263).sum := by decide
  have hdescent : baseEnd_2326263 < baseStart_2326263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326270 : List Nat := [4, 2, 2, 1, 4, 10]
def baseStart_2326270 : Nat := 118140960795 + 2326270 * 2 ^ 59
def prefixEnd_2326270 : Nat := 4983230072969 + 3 ^ 40 * 2326270 * 2
def baseEnd_2326270 : Nat := 4915615811253986385295

theorem tailTrace_2326270 : CollatzResearch.WordTrace tailWord_2326270 prefixEnd_2326270 4915615811253986385295 := by
  unfold tailWord_2326270
  simp only [CollatzResearch.WordTrace]
  refine ⟨10605754660291070016352033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56564024854885706753877509 10605754660291070016352033)
  ·
    refine ⟨7954315995218302512264025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10605754660291070016352033 7954315995218302512264025)
    ·
      refine ⟨5965736996413726884198019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7954315995218302512264025 5965736996413726884198019)
      ·
        refine ⟨8948605494620590326297029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5965736996413726884198019 8948605494620590326297029)
        ·
          refine ⟨1677863530241360686180693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8948605494620590326297029 1677863530241360686180693)
          ·
            refine ⟨4915615811253986385295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1677863530241360686180693 4915615811253986385295)
            ·
              rfl

theorem cell23_2326270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 10].length) (baseStart_2326270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326270 prefixEnd_2326270 := by exact prefixLift 2326270
  have htrace : WordTrace (prefixWord ++ tailWord_2326270) baseStart_2326270 baseEnd_2326270 := by
    simpa [prefixWord, tailWord_2326270, baseEnd_2326270] using wordTrace_append hprefix tailTrace_2326270
  have hstable : (prefixWord ++ tailWord_2326270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326270).length < 2 ^ (prefixWord ++ tailWord_2326270).sum := by decide
  have hdescent : baseEnd_2326270 < baseStart_2326270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326303 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 4]
def baseStart_2326303 : Nat := 118140960795 + 2326303 * 2 ^ 59
def prefixEnd_2326303 : Nat := 4983230072969 + 3 ^ 40 * 2326303 * 2
def baseEnd_2326303 : Nat := 1194511586996317062514033

theorem tailTrace_2326303 : CollatzResearch.WordTrace tailWord_2326303 prefixEnd_2326303 1194511586996317062514033 := by
  unfold tailWord_2326303
  simp only [CollatzResearch.WordTrace]
  refine ⟨84847240891209006766767563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56564827260806004511178375 84847240891209006766767563)
  ·
    refine ⟨127270861336813510150151345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84847240891209006766767563 127270861336813510150151345)
    ·
      refine ⟨95453146002610132612613509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127270861336813510150151345 95453146002610132612613509)
      ·
        refine ⟨17897464875489399864865033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95453146002610132612613509 17897464875489399864865033)
        ·
          refine ⟨13423098656617049898648775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17897464875489399864865033 13423098656617049898648775)
          ·
            refine ⟨20134647984925574847973163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13423098656617049898648775 20134647984925574847973163)
            ·
              refine ⟨30201971977388362271959745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20134647984925574847973163 30201971977388362271959745)
              ·
                refine ⟨22651478983041271703969809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30201971977388362271959745 22651478983041271703969809)
                ·
                  refine ⟨16988609237280953777977357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22651478983041271703969809 16988609237280953777977357)
                  ·
                    refine ⟨6370728463980357666741509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16988609237280953777977357 6370728463980357666741509)
                    ·
                      refine ⟨1194511586996317062514033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6370728463980357666741509 1194511586996317062514033)
                      ·
                        rfl

theorem cell23_2326303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_2326303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326303 prefixEnd_2326303 := by exact prefixLift 2326303
  have htrace : WordTrace (prefixWord ++ tailWord_2326303) baseStart_2326303 baseEnd_2326303 := by
    simpa [prefixWord, tailWord_2326303, baseEnd_2326303] using wordTrace_append hprefix tailTrace_2326303
  have hstable : (prefixWord ++ tailWord_2326303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326303).length < 2 ^ (prefixWord ++ tailWord_2326303).sum := by decide
  have hdescent : baseEnd_2326303 < baseStart_2326303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326318 : List Nat := [4, 1, 3, 2, 3, 1, 2, 1, 1, 2, 3]
def baseStart_2326318 : Nat := 118140960795 + 2326318 * 2 ^ 59
def prefixEnd_2326318 : Nat := 4983230072969 + 3 ^ 40 * 2326318 * 2
def baseEnd_2326318 : Nat := 1194519289206134503826465

theorem tailTrace_2326318 : CollatzResearch.WordTrace tailWord_2326318 prefixEnd_2326318 1194519289206134503826465 := by
  unfold tailWord_2326318
  simp only [CollatzResearch.WordTrace]
  refine ⟨10605973498269333041070451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56565191990769776219042405 10605973498269333041070451)
  ·
    refine ⟨15908960247403999561605677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10605973498269333041070451 15908960247403999561605677)
    ·
      refine ⟨5965860092776499835602129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15908960247403999561605677 5965860092776499835602129)
      ·
        refine ⟨4474395069582374876701597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5965860092776499835602129 4474395069582374876701597)
        ·
          refine ⟨1677898151093390578763099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4474395069582374876701597 1677898151093390578763099)
          ·
            refine ⟨2516847226640085868144649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1677898151093390578763099 2516847226640085868144649)
            ·
              refine ⟨1887635419980064401108487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2516847226640085868144649 1887635419980064401108487)
              ·
                refine ⟨2831453129970096601662731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1887635419980064401108487 2831453129970096601662731)
                ·
                  refine ⟨4247179694955144902494097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2831453129970096601662731 4247179694955144902494097)
                  ·
                    refine ⟨3185384771216358676870573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4247179694955144902494097 3185384771216358676870573)
                    ·
                      refine ⟨1194519289206134503826465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3185384771216358676870573 1194519289206134503826465)
                      ·
                        rfl

theorem cell23_2326318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_2326318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326318 prefixEnd_2326318 := by exact prefixLift 2326318
  have htrace : WordTrace (prefixWord ++ tailWord_2326318) baseStart_2326318 baseEnd_2326318 := by
    simpa [prefixWord, tailWord_2326318, baseEnd_2326318] using wordTrace_append hprefix tailTrace_2326318
  have hstable : (prefixWord ++ tailWord_2326318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326318).length < 2 ^ (prefixWord ++ tailWord_2326318).sum := by decide
  have hdescent : baseEnd_2326318 < baseStart_2326318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326343 : List Nat := [1, 1, 4, 1, 2, 1, 3, 3, 7]
def baseStart_2326343 : Nat := 118140960795 + 2326343 * 2 ^ 59
def prefixEnd_2326343 : Nat := 4983230072969 + 3 ^ 40 * 2326343 * 2
def baseEnd_2326343 : Nat := 132725791802499656223761

theorem tailTrace_2326343 : CollatzResearch.WordTrace tailWord_2326343 prefixEnd_2326343 132725791802499656223761 := by
  unfold tailWord_2326343
  simp only [CollatzResearch.WordTrace]
  refine ⟨84848699811064093598223683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56565799874042729065482455 84848699811064093598223683)
  ·
    refine ⟨127273049716596140397335525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84848699811064093598223683 127273049716596140397335525)
    ·
      refine ⟨23863696821861776324500411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127273049716596140397335525 23863696821861776324500411)
      ·
        refine ⟨35795545232792664486750617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23863696821861776324500411 35795545232792664486750617)
        ·
          refine ⟨26846658924594498365062963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35795545232792664486750617 26846658924594498365062963)
          ·
            refine ⟨40269988386891747547594445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26846658924594498365062963 40269988386891747547594445)
            ·
              refine ⟨15101245645084405330347917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40269988386891747547594445 15101245645084405330347917)
              ·
                refine ⟨5662967116906651998880469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15101245645084405330347917 5662967116906651998880469)
                ·
                  refine ⟨132725791802499656223761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5662967116906651998880469 132725791802499656223761)
                  ·
                    rfl

theorem cell23_2326343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 7].length) (baseStart_2326343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326343 prefixEnd_2326343 := by exact prefixLift 2326343
  have htrace : WordTrace (prefixWord ++ tailWord_2326343) baseStart_2326343 baseEnd_2326343 := by
    simpa [prefixWord, tailWord_2326343, baseEnd_2326343] using wordTrace_append hprefix tailTrace_2326343
  have hstable : (prefixWord ++ tailWord_2326343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326343).length < 2 ^ (prefixWord ++ tailWord_2326343).sum := by decide
  have hdescent : baseEnd_2326343 < baseStart_2326343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326354 : List Nat := [3, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2]
def baseStart_2326354 : Nat := 118140960795 + 2326354 * 2 ^ 59
def prefixEnd_2326354 : Nat := 4983230072969 + 3 ^ 40 * 2326354 * 2
def baseEnd_2326354 : Nat := 1194537774509696362976299

theorem tailTrace_2326354 : CollatzResearch.WordTrace tailWord_2326354 prefixEnd_2326354 1194537774509696362976299 := by
  unfold tailWord_2326354
  simp only [CollatzResearch.WordTrace]
  refine ⟨21212275253506060619218529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56566067342682828317916077 21212275253506060619218529)
  ·
    refine ⟨15909206440129545464413897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21212275253506060619218529 15909206440129545464413897)
    ·
      refine ⟨11931904830097159098310423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15909206440129545464413897 11931904830097159098310423)
      ·
        refine ⟨17897857245145738647465635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11931904830097159098310423 17897857245145738647465635)
        ·
          refine ⟨26846785867718607971198453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17897857245145738647465635 26846785867718607971198453)
          ·
            refine ⟨2516886175098619497299855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26846785867718607971198453 2516886175098619497299855)
            ·
              refine ⟨3775329262647929245949783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2516886175098619497299855 3775329262647929245949783)
              ·
                refine ⟨5662993893971893868924675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3775329262647929245949783 5662993893971893868924675)
                ·
                  refine ⟨8494490840957840803387013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5662993893971893868924675 8494490840957840803387013)
                  ·
                    refine ⟨1592717032679595150635065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8494490840957840803387013 1592717032679595150635065)
                    ·
                      refine ⟨1194537774509696362976299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1592717032679595150635065 1194537774509696362976299)
                      ·
                        rfl

theorem cell23_2326354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_2326354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326354 prefixEnd_2326354 := by exact prefixLift 2326354
  have htrace : WordTrace (prefixWord ++ tailWord_2326354) baseStart_2326354 baseEnd_2326354 := by
    simpa [prefixWord, tailWord_2326354, baseEnd_2326354] using wordTrace_append hprefix tailTrace_2326354
  have hstable : (prefixWord ++ tailWord_2326354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326354).length < 2 ^ (prefixWord ++ tailWord_2326354).sum := by decide
  have hdescent : baseEnd_2326354 < baseStart_2326354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326424 : List Nat := [2, 1, 2, 6, 1, 1, 2, 1, 2, 5]
def baseStart_2326424 : Nat := 118140960795 + 2326424 * 2 ^ 59
def prefixEnd_2326424 : Nat := 4983230072969 + 3 ^ 40 * 2326424 * 2
def baseEnd_2326424 : Nat := 398191239385170363033659

theorem tailTrace_2326424 : CollatzResearch.WordTrace tailWord_2326424 prefixEnd_2326424 398191239385170363033659 := by
  unfold tailWord_2326424
  simp only [CollatzResearch.WordTrace]
  refine ⟨42425827061885322215961163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56567769415847096287948217 42425827061885322215961163)
  ·
    refine ⟨63638740592827983323941745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42425827061885322215961163 63638740592827983323941745)
    ·
      refine ⟨47729055444620987492956309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63638740592827983323941745 47729055444620987492956309)
      ·
        refine ⟨2237299473966608788732327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 47729055444620987492956309 2237299473966608788732327)
        ·
          refine ⟨3355949210949913183098491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2237299473966608788732327 3355949210949913183098491)
          ·
            refine ⟨5033923816424869774647737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3355949210949913183098491 5033923816424869774647737)
            ·
              refine ⟨3775442862318652330985803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5033923816424869774647737 3775442862318652330985803)
              ·
                refine ⟨5663164293477978496478705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3775442862318652330985803 5663164293477978496478705)
                ·
                  refine ⟨4247373220108483872359029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5663164293477978496478705 4247373220108483872359029)
                  ·
                    refine ⟨398191239385170363033659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4247373220108483872359029 398191239385170363033659)
                    ·
                      rfl

theorem cell23_2326424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 2, 5].length) (baseStart_2326424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326424 prefixEnd_2326424 := by exact prefixLift 2326424
  have htrace : WordTrace (prefixWord ++ tailWord_2326424) baseStart_2326424 baseEnd_2326424 := by
    simpa [prefixWord, tailWord_2326424, baseEnd_2326424] using wordTrace_append hprefix tailTrace_2326424
  have hstable : (prefixWord ++ tailWord_2326424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326424).length < 2 ^ (prefixWord ++ tailWord_2326424).sum := by decide
  have hdescent : baseEnd_2326424 < baseStart_2326424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326480 : List Nat := [2, 1, 1, 1, 1, 2, 6, 1, 3, 5]
def baseStart_2326480 : Nat := 118140960795 + 2326480 * 2 ^ 59
def prefixEnd_2326480 : Nat := 4983230072969 + 3 ^ 40 * 2326480 * 2
def baseEnd_2326480 : Nat := 398200824357387623333573

theorem tailTrace_2326480 : CollatzResearch.WordTrace tailWord_2326480 prefixEnd_2326480 398200824357387623333573 := by
  unfold tailWord_2326480
  simp only [CollatzResearch.WordTrace]
  refine ⟨42426848305783882997980447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56569131074378510663973929 42426848305783882997980447)
  ·
    refine ⟨63640272458675824496970671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42426848305783882997980447 63640272458675824496970671)
    ·
      refine ⟨95460408688013736745456007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63640272458675824496970671 95460408688013736745456007)
      ·
        refine ⟨143190613032020605118184011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95460408688013736745456007 143190613032020605118184011)
        ·
          refine ⟨214785919548030907677276017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143190613032020605118184011 214785919548030907677276017)
          ·
            refine ⟨161089439661023180757957013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214785919548030907677276017 161089439661023180757957013)
            ·
              refine ⟨7551067484110461598029235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 161089439661023180757957013 7551067484110461598029235)
              ·
                refine ⟨11326601226165692397043853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7551067484110461598029235 11326601226165692397043853)
                ·
                  refine ⟨4247475459812134648891445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11326601226165692397043853 4247475459812134648891445)
                  ·
                    refine ⟨398200824357387623333573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4247475459812134648891445 398200824357387623333573)
                    ·
                      rfl

theorem cell23_2326480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 3, 5].length) (baseStart_2326480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326480 prefixEnd_2326480 := by exact prefixLift 2326480
  have htrace : WordTrace (prefixWord ++ tailWord_2326480) baseStart_2326480 baseEnd_2326480 := by
    simpa [prefixWord, tailWord_2326480, baseEnd_2326480] using wordTrace_append hprefix tailTrace_2326480
  have hstable : (prefixWord ++ tailWord_2326480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326480).length < 2 ^ (prefixWord ++ tailWord_2326480).sum := by decide
  have hdescent : baseEnd_2326480 < baseStart_2326480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326487 : List Nat := [1, 1, 3, 2, 1, 1, 5, 1, 1, 5, 2]
def baseStart_2326487 : Nat := 118140960795 + 2326487 * 2 ^ 59
def prefixEnd_2326487 : Nat := 4983230072969 + 3 ^ 40 * 2326487 * 2
def baseEnd_2326487 : Nat := 1194606067436744342613187

theorem tailTrace_2326487 : CollatzResearch.WordTrace tailWord_2326487 prefixEnd_2326487 1194606067436744342613187 := by
  unfold tailWord_2326487
  simp only [CollatzResearch.WordTrace]
  refine ⟨84853951922542406191465715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56569301281694937460977143 84853951922542406191465715)
  ·
    refine ⟨127280927883813609287198573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84853951922542406191465715 127280927883813609287198573)
    ·
      refine ⟨47730347956430103482699465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127280927883813609287198573 47730347956430103482699465)
      ·
        refine ⟨35797760967322577612024599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47730347956430103482699465 35797760967322577612024599)
        ·
          refine ⟨53696641450983866418036899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35797760967322577612024599 53696641450983866418036899)
          ·
            refine ⟨80544962176475799627055349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53696641450983866418036899 80544962176475799627055349)
            ·
              refine ⟨7551090204044606215036439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80544962176475799627055349 7551090204044606215036439)
              ·
                refine ⟨11326635306066909322554659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7551090204044606215036439 11326635306066909322554659)
                ·
                  refine ⟨16989952959100363983831989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11326635306066909322554659 16989952959100363983831989)
                  ·
                    refine ⟨1592808089915659123484249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16989952959100363983831989 1592808089915659123484249)
                    ·
                      refine ⟨1194606067436744342613187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1592808089915659123484249 1194606067436744342613187)
                      ·
                        rfl

theorem cell23_2326487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 5, 2].length) (baseStart_2326487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326487 prefixEnd_2326487 := by exact prefixLift 2326487
  have htrace : WordTrace (prefixWord ++ tailWord_2326487) baseStart_2326487 baseEnd_2326487 := by
    simpa [prefixWord, tailWord_2326487, baseEnd_2326487] using wordTrace_append hprefix tailTrace_2326487
  have hstable : (prefixWord ++ tailWord_2326487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326487).length < 2 ^ (prefixWord ++ tailWord_2326487).sum := by decide
  have hdescent : baseEnd_2326487 < baseStart_2326487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326520 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 3, 1, 5]
def baseStart_2326520 : Nat := 118140960795 + 2326520 * 2 ^ 59
def prefixEnd_2326520 : Nat := 4983230072969 + 3 ^ 40 * 2326520 * 2
def baseEnd_2326520 : Nat := 1194623012298342713500535

theorem tailTrace_2326520 : CollatzResearch.WordTrace tailWord_2326520 prefixEnd_2326520 1194623012298342713500535 := by
  unfold tailWord_2326520
  simp only [CollatzResearch.WordTrace]
  refine ⟨42427577765711426413708507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56570103687615235218278009 42427577765711426413708507)
  ·
    refine ⟨63641366648567139620562761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42427577765711426413708507 63641366648567139620562761)
    ·
      refine ⟨47731024986425354715422071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63641366648567139620562761 47731024986425354715422071)
      ·
        refine ⟨71596537479638032073133107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47731024986425354715422071 71596537479638032073133107)
        ·
          refine ⟨107394806219457048109699661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71596537479638032073133107 107394806219457048109699661)
          ·
            refine ⟨40273052332296393041137373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107394806219457048109699661 40273052332296393041137373)
            ·
              refine ⟨15102394624611147390426515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40273052332296393041137373 15102394624611147390426515)
              ·
                refine ⟨22653591936916721085639773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15102394624611147390426515 22653591936916721085639773)
                ·
                  refine ⟨8495096976343770407114915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22653591936916721085639773 8495096976343770407114915)
                  ·
                    refine ⟨12742645464515655610672373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8495096976343770407114915 12742645464515655610672373)
                    ·
                      refine ⟨1194623012298342713500535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12742645464515655610672373 1194623012298342713500535)
                      ·
                        rfl

theorem cell23_2326520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_2326520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326520 prefixEnd_2326520 := by exact prefixLift 2326520
  have htrace : WordTrace (prefixWord ++ tailWord_2326520) baseStart_2326520 baseEnd_2326520 := by
    simpa [prefixWord, tailWord_2326520, baseEnd_2326520] using wordTrace_append hprefix tailTrace_2326520
  have hstable : (prefixWord ++ tailWord_2326520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326520).length < 2 ^ (prefixWord ++ tailWord_2326520).sum := by decide
  have hdescent : baseEnd_2326520 < baseStart_2326520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326527 : List Nat := [1, 1, 2, 2, 1, 2, 1, 7, 2, 4]
def baseStart_2326527 : Nat := 118140960795 + 2326527 * 2 ^ 59
def prefixEnd_2326527 : Nat := 4983230072969 + 3 ^ 40 * 2326527 * 2
def baseEnd_2326527 : Nat := 398208868887641395371001

theorem tailTrace_2326527 : CollatzResearch.WordTrace tailWord_2326527 prefixEnd_2326527 398208868887641395371001 := by
  unfold tailWord_2326527
  simp only [CollatzResearch.WordTrace]
  refine ⟨84855410842397493022921835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56570273894931662015281223 84855410842397493022921835)
  ·
    refine ⟨127283116263596239534382753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84855410842397493022921835 127283116263596239534382753)
    ·
      refine ⟨95462337197697179650787065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127283116263596239534382753 95462337197697179650787065)
      ·
        refine ⟨71596752898272884738090299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95462337197697179650787065 71596752898272884738090299)
        ·
          refine ⟨107395129347409327107135449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71596752898272884738090299 107395129347409327107135449)
          ·
            refine ⟨80546347010556995330351587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107395129347409327107135449 80546347010556995330351587)
            ·
              refine ⟨120819520515835492995527381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80546347010556995330351587 120819520515835492995527381)
              ·
                refine ⟨2831707512089894367082673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 120819520515835492995527381 2831707512089894367082673)
                ·
                  refine ⟨2123780634067420775312005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2831707512089894367082673 2123780634067420775312005)
                  ·
                    refine ⟨398208868887641395371001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2123780634067420775312005 398208868887641395371001)
                    ·
                      rfl

theorem cell23_2326527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 2, 4].length) (baseStart_2326527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326527 prefixEnd_2326527 := by exact prefixLift 2326527
  have htrace : WordTrace (prefixWord ++ tailWord_2326527) baseStart_2326527 baseEnd_2326527 := by
    simpa [prefixWord, tailWord_2326527, baseEnd_2326527] using wordTrace_append hprefix tailTrace_2326527
  have hstable : (prefixWord ++ tailWord_2326527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326527).length < 2 ^ (prefixWord ++ tailWord_2326527).sum := by decide
  have hdescent : baseEnd_2326527 < baseStart_2326527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326540 : List Nat := [2, 2, 1, 2, 3, 1, 3, 9]
def baseStart_2326540 : Nat := 118140960795 + 2326540 * 2 ^ 59
def prefixEnd_2326540 : Nat := 4983230072969 + 3 ^ 40 * 2326540 * 2
def baseEnd_2326540 : Nat := 44245677107830838342609

theorem tailTrace_2326540 : CollatzResearch.WordTrace tailWord_2326540 prefixEnd_2326540 44245677107830838342609 := by
  unfold tailWord_2326540
  simp only [CollatzResearch.WordTrace]
  refine ⟨42427942495675198121572537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56570589994233597495430049 42427942495675198121572537)
  ·
    refine ⟨31820956871756398591179403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42427942495675198121572537 31820956871756398591179403)
    ·
      refine ⟨47731435307634597886769105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31820956871756398591179403 47731435307634597886769105)
      ·
        refine ⟨35798576480725948415076829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47731435307634597886769105 35798576480725948415076829)
        ·
          refine ⟨13424466180272230655653811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35798576480725948415076829 13424466180272230655653811)
          ·
            refine ⟨20136699270408345983480717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13424466180272230655653811 20136699270408345983480717)
            ·
              refine ⟨7551262226403129743805269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20136699270408345983480717 7551262226403129743805269)
              ·
                refine ⟨44245677107830838342609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7551262226403129743805269 44245677107830838342609)
                ·
                  rfl

theorem cell23_2326540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 9].length) (baseStart_2326540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326540 prefixEnd_2326540 := by exact prefixLift 2326540
  have htrace : WordTrace (prefixWord ++ tailWord_2326540) baseStart_2326540 baseEnd_2326540 := by
    simpa [prefixWord, tailWord_2326540, baseEnd_2326540] using wordTrace_append hprefix tailTrace_2326540
  have hstable : (prefixWord ++ tailWord_2326540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326540).length < 2 ^ (prefixWord ++ tailWord_2326540).sum := by decide
  have hdescent : baseEnd_2326540 < baseStart_2326540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326554 : List Nat := [3, 1, 1, 3, 1, 3, 2, 3, 1, 2, 3]
def baseStart_2326554 : Nat := 118140960795 + 2326554 * 2 ^ 59
def prefixEnd_2326554 : Nat := 4983230072969 + 3 ^ 40 * 2326554 * 2
def baseEnd_2326554 : Nat := 1194640470640595580475379

theorem tailTrace_2326554 : CollatzResearch.WordTrace tailWord_2326554 prefixEnd_2326554 1194640470640595580475379 := by
  unfold tailWord_2326554
  simp only [CollatzResearch.WordTrace]
  refine ⟨21214098903324919158538679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56570930408866451089436477 21214098903324919158538679)
  ·
    refine ⟨31821148354987378737808019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21214098903324919158538679 31821148354987378737808019)
    ·
      refine ⟨47731722532481068106712029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31821148354987378737808019 47731722532481068106712029)
      ·
        refine ⟨17899395949680400540017011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47731722532481068106712029 17899395949680400540017011)
        ·
          refine ⟨26849093924520600810025517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17899395949680400540017011 26849093924520600810025517)
          ·
            refine ⟨10068410221695225303759569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26849093924520600810025517 10068410221695225303759569)
            ·
              refine ⟨7551307666271418977819677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10068410221695225303759569 7551307666271418977819677)
              ·
                refine ⟨2831740374851782116682379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7551307666271418977819677 2831740374851782116682379)
                ·
                  refine ⟨4247610562277673175023569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2831740374851782116682379 4247610562277673175023569)
                  ·
                    refine ⟨3185707921708254881267677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4247610562277673175023569 3185707921708254881267677)
                    ·
                      refine ⟨1194640470640595580475379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3185707921708254881267677 1194640470640595580475379)
                      ·
                        rfl

theorem cell23_2326554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_2326554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326554 prefixEnd_2326554 := by exact prefixLift 2326554
  have htrace : WordTrace (prefixWord ++ tailWord_2326554) baseStart_2326554 baseEnd_2326554 := by
    simpa [prefixWord, tailWord_2326554, baseEnd_2326554] using wordTrace_append hprefix tailTrace_2326554
  have hstable : (prefixWord ++ tailWord_2326554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326554).length < 2 ^ (prefixWord ++ tailWord_2326554).sum := by decide
  have hdescent : baseEnd_2326554 < baseStart_2326554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326557 : List Nat := [1, 4, 2, 2, 2, 3, 9]
def baseStart_2326557 : Nat := 118140960795 + 2326557 * 2 ^ 59
def prefixEnd_2326557 : Nat := 4983230072969 + 3 ^ 40 * 2326557 * 2
def baseEnd_2326557 : Nat := 14748666803488383564665

theorem tailTrace_2326557 : CollatzResearch.WordTrace tailWord_2326557 prefixEnd_2326557 14748666803488383564665 := by
  unfold tailWord_2326557
  simp only [CollatzResearch.WordTrace]
  refine ⟨84856505032288808146513925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56571003354859205431009283 84856505032288808146513925)
  ·
    refine ⟨15910594693554151527471361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84856505032288808146513925 15910594693554151527471361)
    ·
      refine ⟨11932946020165613645603521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15910594693554151527471361 11932946020165613645603521)
      ·
        refine ⟨8949709515124210234202641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11932946020165613645603521 8949709515124210234202641)
        ·
          refine ⟨6712282136343157675651981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8949709515124210234202641 6712282136343157675651981)
          ·
            refine ⟨2517105801128684128369493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6712282136343157675651981 2517105801128684128369493)
            ·
              refine ⟨14748666803488383564665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2517105801128684128369493 14748666803488383564665)
              ·
                rfl

theorem cell23_2326557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 9].length) (baseStart_2326557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326557 prefixEnd_2326557 := by exact prefixLift 2326557
  have htrace : WordTrace (prefixWord ++ tailWord_2326557) baseStart_2326557 baseEnd_2326557 := by
    simpa [prefixWord, tailWord_2326557, baseEnd_2326557] using wordTrace_append hprefix tailTrace_2326557
  have hstable : (prefixWord ++ tailWord_2326557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326557).length < 2 ^ (prefixWord ++ tailWord_2326557).sum := by decide
  have hdescent : baseEnd_2326557 < baseStart_2326557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326600 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 3, 8]
def baseStart_2326600 : Nat := 118140960795 + 2326600 * 2 ^ 59
def prefixEnd_2326600 : Nat := 4983230072969 + 3 ^ 40 * 2326600 * 2
def baseEnd_2326600 : Nat := 398221363583567466833389

theorem tailTrace_2326600 : CollatzResearch.WordTrace tailWord_2326600 prefixEnd_2326600 398221363583567466833389 := by
  unfold tailWord_2326600
  simp only [CollatzResearch.WordTrace]
  refine ⟨42429036685566513245164627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56572048914088684326886169 42429036685566513245164627)
  ·
    refine ⟨63643555028349769867746941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42429036685566513245164627 63643555028349769867746941)
    ·
      refine ⟨23866333135631163700405103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63643555028349769867746941 23866333135631163700405103)
      ·
        refine ⟨35799499703446745550607655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23866333135631163700405103 35799499703446745550607655)
        ·
          refine ⟨53699249555170118325911483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35799499703446745550607655 53699249555170118325911483)
          ·
            refine ⟨80548874332755177488867225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53699249555170118325911483 80548874332755177488867225)
            ·
              refine ⟨60411655749566383116650419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80548874332755177488867225 60411655749566383116650419)
              ·
                refine ⟨90617483624349574674975629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60411655749566383116650419 90617483624349574674975629)
                ·
                  refine ⟨33981556359131090503115861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90617483624349574674975629 33981556359131090503115861)
                  ·
                    refine ⟨398221363583567466833389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33981556359131090503115861 398221363583567466833389)
                    ·
                      rfl

theorem cell23_2326600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_2326600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326600 prefixEnd_2326600 := by exact prefixLift 2326600
  have htrace : WordTrace (prefixWord ++ tailWord_2326600) baseStart_2326600 baseEnd_2326600 := by
    simpa [prefixWord, tailWord_2326600, baseEnd_2326600] using wordTrace_append hprefix tailTrace_2326600
  have hstable : (prefixWord ++ tailWord_2326600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326600).length < 2 ^ (prefixWord ++ tailWord_2326600).sum := by decide
  have hdescent : baseEnd_2326600 < baseStart_2326600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326627 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 2, 4, 3]
def baseStart_2326627 : Nat := 118140960795 + 2326627 * 2 ^ 59
def prefixEnd_2326627 : Nat := 4983230072969 + 3 ^ 40 * 2326627 * 2
def baseEnd_2326627 : Nat := 1194677954728373794862543

theorem tailTrace_2326627 : CollatzResearch.WordTrace tailWord_2326627 prefixEnd_2326627 1194677954728373794862543 := by
  unfold tailWord_2326627
  simp only [CollatzResearch.WordTrace]
  refine ⟨84859058142035210101562135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56572705428023473401041423 84859058142035210101562135)
  ·
    refine ⟨127288587213052815152343203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84859058142035210101562135 127288587213052815152343203)
    ·
      refine ⟨190932880819579222728514805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127288587213052815152343203 190932880819579222728514805)
      ·
        refine ⟨17899957576835552130798263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 190932880819579222728514805 17899957576835552130798263)
        ·
          refine ⟨26849936365253328196197395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17899957576835552130798263 26849936365253328196197395)
          ·
            refine ⟨40274904547879992294296093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26849936365253328196197395 40274904547879992294296093)
            ·
              refine ⟨15103089205454997110361035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40274904547879992294296093 15103089205454997110361035)
              ·
                refine ⟨22654633808182495665541553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15103089205454997110361035 22654633808182495665541553)
                ·
                  refine ⟨16990975356136871749156165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22654633808182495665541553 16990975356136871749156165)
                  ·
                    refine ⟨3185807879275663452966781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16990975356136871749156165 3185807879275663452966781)
                    ·
                      refine ⟨1194677954728373794862543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3185807879275663452966781 1194677954728373794862543)
                      ·
                        rfl

theorem cell23_2326627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_2326627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326627 prefixEnd_2326627 := by exact prefixLift 2326627
  have htrace : WordTrace (prefixWord ++ tailWord_2326627) baseStart_2326627 baseEnd_2326627 := by
    simpa [prefixWord, tailWord_2326627, baseEnd_2326627] using wordTrace_append hprefix tailTrace_2326627
  have hstable : (prefixWord ++ tailWord_2326627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326627).length < 2 ^ (prefixWord ++ tailWord_2326627).sum := by decide
  have hdescent : baseEnd_2326627 < baseStart_2326627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326634 : List Nat := [3, 1, 3, 2, 3, 1, 1, 1, 2, 6]
def baseStart_2326634 : Nat := 118140960795 + 2326634 * 2 ^ 59
def prefixEnd_2326634 : Nat := 4983230072969 + 3 ^ 40 * 2326634 * 2
def baseEnd_2326634 : Nat := 398227183030985089158337

theorem tailTrace_2326634 : CollatzResearch.WordTrace tailWord_2326634 prefixEnd_2326634 398227183030985089158337 := by
  unfold tailWord_2326634
  simp only [CollatzResearch.WordTrace]
  refine ⟨21214828363252462574266739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56572875635339900198044637 21214828363252462574266739)
  ·
    refine ⟨31822242544878693861400109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21214828363252462574266739 31822242544878693861400109)
    ·
      refine ⟨11933340954329510198025041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31822242544878693861400109 11933340954329510198025041)
      ·
        refine ⟨8950005715747132648518781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11933340954329510198025041 8950005715747132648518781)
        ·
          refine ⟨3356252143405174743194543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8950005715747132648518781 3356252143405174743194543)
          ·
            refine ⟨5034378215107762114791815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3356252143405174743194543 5034378215107762114791815)
            ·
              refine ⟨7551567322661643172187723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5034378215107762114791815 7551567322661643172187723)
              ·
                refine ⟨11327350983992464758281585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7551567322661643172187723 11327350983992464758281585)
                ·
                  refine ⟨8495513237994348568711189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11327350983992464758281585 8495513237994348568711189)
                  ·
                    refine ⟨398227183030985089158337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8495513237994348568711189 398227183030985089158337)
                    ·
                      rfl

theorem cell23_2326634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_2326634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326634 prefixEnd_2326634 := by exact prefixLift 2326634
  have htrace : WordTrace (prefixWord ++ tailWord_2326634) baseStart_2326634 baseEnd_2326634 := by
    simpa [prefixWord, tailWord_2326634, baseEnd_2326634] using wordTrace_append hprefix tailTrace_2326634
  have hstable : (prefixWord ++ tailWord_2326634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326634).length < 2 ^ (prefixWord ++ tailWord_2326634).sum := by decide
  have hdescent : baseEnd_2326634 < baseStart_2326634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326641 : List Nat := [1, 2, 2, 2, 1, 1, 3, 5, 2, 2, 2]
def baseStart_2326641 : Nat := 118140960795 + 2326641 * 2 ^ 59
def prefixEnd_2326641 : Nat := 4983230072969 + 3 ^ 40 * 2326641 * 2
def baseEnd_2326641 : Nat := 1194685143457536740087479

theorem tailTrace_2326641 : CollatzResearch.WordTrace tailWord_2326641 prefixEnd_2326641 1194685143457536740087479 := by
  unfold tailWord_2326641
  simp only [CollatzResearch.WordTrace]
  refine ⟨84859568763984490492571777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56573045842656326995047851 84859568763984490492571777)
  ·
    refine ⟨63644676572988367869428833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84859568763984490492571777 63644676572988367869428833)
    ·
      refine ⟨47733507429741275902071625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63644676572988367869428833 47733507429741275902071625)
      ·
        refine ⟨35800130572305956926553719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47733507429741275902071625 35800130572305956926553719)
        ·
          refine ⟨53700195858458935389830579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35800130572305956926553719 53700195858458935389830579)
          ·
            refine ⟨80550293787688403084745869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53700195858458935389830579 80550293787688403084745869)
            ·
              refine ⟨30206360170383151156779701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80550293787688403084745869 30206360170383151156779701)
              ·
                refine ⟨2831846265973420420948097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30206360170383151156779701 2831846265973420420948097)
                ·
                  refine ⟨2123884699480065315711073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2831846265973420420948097 2123884699480065315711073)
                  ·
                    refine ⟨1592913524610048986783305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2123884699480065315711073 1592913524610048986783305)
                    ·
                      refine ⟨1194685143457536740087479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1592913524610048986783305 1194685143457536740087479)
                      ·
                        rfl

theorem cell23_2326641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 2, 2, 2].length) (baseStart_2326641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326641 prefixEnd_2326641 := by exact prefixLift 2326641
  have htrace : WordTrace (prefixWord ++ tailWord_2326641) baseStart_2326641 baseEnd_2326641 := by
    simpa [prefixWord, tailWord_2326641, baseEnd_2326641] using wordTrace_append hprefix tailTrace_2326641
  have hstable : (prefixWord ++ tailWord_2326641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326641).length < 2 ^ (prefixWord ++ tailWord_2326641).sum := by decide
  have hdescent : baseEnd_2326641 < baseStart_2326641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326647 : List Nat := [1, 1, 3, 1, 1, 6, 1, 2, 7]
def baseStart_2326647 : Nat := 118140960795 + 2326647 * 2 ^ 59
def prefixEnd_2326647 : Nat := 4983230072969 + 3 ^ 40 * 2326647 * 2
def baseEnd_2326647 : Nat := 132743136037940412956939

theorem tailTrace_2326647 : CollatzResearch.WordTrace tailWord_2326647 prefixEnd_2326647 132743136037940412956939 := by
  unfold tailWord_2326647
  simp only [CollatzResearch.WordTrace]
  refine ⟨84859787601962753517290195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56573191734641835678193463 84859787601962753517290195)
  ·
    refine ⟨127289681402944130275935293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84859787601962753517290195 127289681402944130275935293)
    ·
      refine ⟨47733630526104048853475735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127289681402944130275935293 47733630526104048853475735)
      ·
        refine ⟨71600445789156073280213603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47733630526104048853475735 71600445789156073280213603)
        ·
          refine ⟨107400668683734109920320405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71600445789156073280213603 107400668683734109920320405)
          ·
            refine ⟨5034406344550036402515019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 107400668683734109920320405 5034406344550036402515019)
            ·
              refine ⟨7551609516825054603772529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5034406344550036402515019 7551609516825054603772529)
              ·
                refine ⟨5663707137618790952829397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7551609516825054603772529 5663707137618790952829397)
                ·
                  refine ⟨132743136037940412956939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5663707137618790952829397 132743136037940412956939)
                  ·
                    rfl

theorem cell23_2326647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 7].length) (baseStart_2326647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326647 prefixEnd_2326647 := by exact prefixLift 2326647
  have htrace : WordTrace (prefixWord ++ tailWord_2326647) baseStart_2326647 baseEnd_2326647 := by
    simpa [prefixWord, tailWord_2326647, baseEnd_2326647] using wordTrace_append hprefix tailTrace_2326647
  have hstable : (prefixWord ++ tailWord_2326647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326647).length < 2 ^ (prefixWord ++ tailWord_2326647).sum := by decide
  have hdescent : baseEnd_2326647 < baseStart_2326647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326674 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 4, 3, 3]
def baseStart_2326674 : Nat := 118140960795 + 2326674 * 2 ^ 59
def prefixEnd_2326674 : Nat := 4983230072969 + 3 ^ 40 * 2326674 * 2
def baseEnd_2326674 : Nat := 1194702088319135110974827

theorem tailTrace_2326674 : CollatzResearch.WordTrace tailWord_2326674 prefixEnd_2326674 1194702088319135110974827 := by
  unfold tailWord_2326674
  simp only [CollatzResearch.WordTrace]
  refine ⟨21215193093216234282130769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56573848248576624752348717 21215193093216234282130769)
  ·
    refine ⟨15911394819912175711598077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21215193093216234282130769 15911394819912175711598077)
    ·
      refine ⟨5966773057467065891849279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15911394819912175711598077 5966773057467065891849279)
      ·
        refine ⟨8950159586200598837773919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5966773057467065891849279 8950159586200598837773919)
        ·
          refine ⟨13425239379300898256660879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8950159586200598837773919 13425239379300898256660879)
          ·
            refine ⟨20137859068951347384991319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13425239379300898256660879 20137859068951347384991319)
            ·
              refine ⟨30206788603427021077486979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20137859068951347384991319 30206788603427021077486979)
              ·
                refine ⟨45310182905140531616230469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30206788603427021077486979 45310182905140531616230469)
                ·
                  refine ⟨8495659294713849678043213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45310182905140531616230469 8495659294713849678043213)
                  ·
                    refine ⟨3185872235517693629266205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8495659294713849678043213 3185872235517693629266205)
                    ·
                      refine ⟨1194702088319135110974827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3185872235517693629266205 1194702088319135110974827)
                      ·
                        rfl

theorem cell23_2326674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_2326674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326674 prefixEnd_2326674 := by exact prefixLift 2326674
  have htrace : WordTrace (prefixWord ++ tailWord_2326674) baseStart_2326674 baseEnd_2326674 := by
    simpa [prefixWord, tailWord_2326674, baseEnd_2326674] using wordTrace_append hprefix tailTrace_2326674
  have hstable : (prefixWord ++ tailWord_2326674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326674).length < 2 ^ (prefixWord ++ tailWord_2326674).sum := by decide
  have hdescent : baseEnd_2326674 < baseStart_2326674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326677 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 4, 5]
def baseStart_2326677 : Nat := 118140960795 + 2326677 * 2 ^ 59
def prefixEnd_2326677 : Nat := 4983230072969 + 3 ^ 40 * 2326677 * 2
def baseEnd_2326677 : Nat := 398234542920366199745771

theorem tailTrace_2326677 : CollatzResearch.WordTrace tailWord_2326677 prefixEnd_2326677 398234542920366199745771 := by
  unfold tailWord_2326677
  simp only [CollatzResearch.WordTrace]
  refine ⟨84860881791854068640882285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56573921194569379093921523 84860881791854068640882285)
  ·
    refine ⟨31822830671945275740330857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84860881791854068640882285 31822830671945275740330857)
    ·
      refine ⟨23867123003958956805248143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31822830671945275740330857 23867123003958956805248143)
      ·
        refine ⟨35800684505938435207872215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23867123003958956805248143 35800684505938435207872215)
        ·
          refine ⟨53701026758907652811808323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35800684505938435207872215 53701026758907652811808323)
          ·
            refine ⟨80551540138361479217712485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53701026758907652811808323 80551540138361479217712485)
            ·
              refine ⟨15103413775942777353321091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80551540138361479217712485 15103413775942777353321091)
              ·
                refine ⟨22655120663914166029981637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15103413775942777353321091 22655120663914166029981637)
                ·
                  refine ⟨4247835124483906130621557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22655120663914166029981637 4247835124483906130621557)
                  ·
                    refine ⟨398234542920366199745771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4247835124483906130621557 398234542920366199745771)
                    ·
                      rfl

theorem cell23_2326677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_2326677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326677 prefixEnd_2326677 := by exact prefixLift 2326677
  have htrace : WordTrace (prefixWord ++ tailWord_2326677) baseStart_2326677 baseEnd_2326677 := by
    simpa [prefixWord, tailWord_2326677, baseEnd_2326677] using wordTrace_append hprefix tailTrace_2326677
  have hstable : (prefixWord ++ tailWord_2326677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326677).length < 2 ^ (prefixWord ++ tailWord_2326677).sum := by decide
  have hdescent : baseEnd_2326677 < baseStart_2326677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326714 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 1, 6, 2]
def baseStart_2326714 : Nat := 118140960795 + 2326714 * 2 ^ 59
def prefixEnd_2326714 : Nat := 4983230072969 + 3 ^ 40 * 2326714 * 2
def baseEnd_2326714 : Nat := 1194722627545314954474643

theorem tailTrace_2326714 : CollatzResearch.WordTrace tailWord_2326714 prefixEnd_2326714 1194722627545314954474643 := by
  unfold tailWord_2326714
  simp only [CollatzResearch.WordTrace]
  refine ⟨21215557823180005989994799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56574820861813349306652797 21215557823180005989994799)
  ·
    refine ⟨31823336734770008984992199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21215557823180005989994799 31823336734770008984992199)
    ·
      refine ⟨47735005102155013477488299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31823336734770008984992199 47735005102155013477488299)
      ·
        refine ⟨71602507653232520216232449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47735005102155013477488299 71602507653232520216232449)
        ·
          refine ⟨53701880739924390162174337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71602507653232520216232449 53701880739924390162174337)
          ·
            refine ⟨40276410554943292621630753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53701880739924390162174337 40276410554943292621630753)
            ·
              refine ⟨30207307916207469466223065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40276410554943292621630753 30207307916207469466223065)
              ·
                refine ⟨22655480937155602099667299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30207307916207469466223065 22655480937155602099667299)
                ·
                  refine ⟨33983221405733403149500949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22655480937155602099667299 33983221405733403149500949)
                  ·
                    refine ⟨1592963503393753272632857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 33983221405733403149500949 1592963503393753272632857)
                    ·
                      refine ⟨1194722627545314954474643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1592963503393753272632857 1194722627545314954474643)
                      ·
                        rfl

theorem cell23_2326714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 1, 6, 2].length) (baseStart_2326714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326714 prefixEnd_2326714 := by exact prefixLift 2326714
  have htrace : WordTrace (prefixWord ++ tailWord_2326714) baseStart_2326714 baseEnd_2326714 := by
    simpa [prefixWord, tailWord_2326714, baseEnd_2326714] using wordTrace_append hprefix tailTrace_2326714
  have hstable : (prefixWord ++ tailWord_2326714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326714).length < 2 ^ (prefixWord ++ tailWord_2326714).sum := by decide
  have hdescent : baseEnd_2326714 < baseStart_2326714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326717 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 2, 3, 5]
def baseStart_2326717 : Nat := 118140960795 + 2326717 * 2 ^ 59
def prefixEnd_2326717 : Nat := 4983230072969 + 3 ^ 40 * 2326717 * 2
def baseEnd_2326717 : Nat := 1194724167987278442737129

theorem tailTrace_2326717 : CollatzResearch.WordTrace tailWord_2326717 prefixEnd_2326717 1194724167987278442737129 := by
  unfold tailWord_2326717
  simp only [CollatzResearch.WordTrace]
  refine ⟨84862340711709155472338405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56574893807806103648225603 84862340711709155472338405)
  ·
    refine ⟨15911688883445466651063451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84862340711709155472338405 15911688883445466651063451)
    ·
      refine ⟨23867533325168199976595177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15911688883445466651063451 23867533325168199976595177)
      ·
        refine ⟨17900649993876149982446383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23867533325168199976595177 17900649993876149982446383)
        ·
          refine ⟨26850974990814224973669575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17900649993876149982446383 26850974990814224973669575)
          ·
            refine ⟨40276462486221337460504363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26850974990814224973669575 40276462486221337460504363)
            ·
              refine ⟨60414693729332006190756545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40276462486221337460504363 60414693729332006190756545)
              ·
                refine ⟨45311020296999004643067409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60414693729332006190756545 45311020296999004643067409)
                ·
                  refine ⟨33983265222749253482300557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45311020296999004643067409 33983265222749253482300557)
                  ·
                    refine ⟨12743724458530970055862709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33983265222749253482300557 12743724458530970055862709)
                    ·
                      refine ⟨1194724167987278442737129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12743724458530970055862709 1194724167987278442737129)
                      ·
                        rfl

theorem cell23_2326717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_2326717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326717 prefixEnd_2326717 := by exact prefixLift 2326717
  have htrace : WordTrace (prefixWord ++ tailWord_2326717) baseStart_2326717 baseEnd_2326717 := by
    simpa [prefixWord, tailWord_2326717, baseEnd_2326717] using wordTrace_append hprefix tailTrace_2326717
  have hstable : (prefixWord ++ tailWord_2326717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326717).length < 2 ^ (prefixWord ++ tailWord_2326717).sum := by decide
  have hdescent : baseEnd_2326717 < baseStart_2326717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326737 : List Nat := [1, 2, 2, 1, 2, 2, 4, 1, 8]
def baseStart_2326737 : Nat := 118140960795 + 2326737 * 2 ^ 59
def prefixEnd_2326737 : Nat := 4983230072969 + 3 ^ 40 * 2326737 * 2
def baseEnd_2326737 : Nat := 132748270844485373831893

theorem tailTrace_2326737 : CollatzResearch.WordTrace tailWord_2326737 prefixEnd_2326737 132748270844485373831893 := by
  unfold tailWord_2326737
  simp only [CollatzResearch.WordTrace]
  refine ⟨84863070171636698888066465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56575380114424465925377643 84863070171636698888066465)
  ·
    refine ⟨63647302628727524166049849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84863070171636698888066465 63647302628727524166049849)
    ·
      refine ⟨47735476971545643124537387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63647302628727524166049849 47735476971545643124537387)
      ·
        refine ⟨71603215457318464686806081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47735476971545643124537387 71603215457318464686806081)
        ·
          refine ⟨53702411592988848515104561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71603215457318464686806081 53702411592988848515104561)
          ·
            refine ⟨40276808694741636386328421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53702411592988848515104561 40276808694741636386328421)
            ·
              refine ⟨7551901630264056822436579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40276808694741636386328421 7551901630264056822436579)
              ·
                refine ⟨11327852445396085233654869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7551901630264056822436579 11327852445396085233654869)
                ·
                  refine ⟨132748270844485373831893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11327852445396085233654869 132748270844485373831893)
                  ·
                    rfl

theorem cell23_2326737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 8].length) (baseStart_2326737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326737 prefixEnd_2326737 := by exact prefixLift 2326737
  have htrace : WordTrace (prefixWord ++ tailWord_2326737) baseStart_2326737 baseEnd_2326737 := by
    simpa [prefixWord, tailWord_2326737, baseEnd_2326737] using wordTrace_append hprefix tailTrace_2326737
  have hstable : (prefixWord ++ tailWord_2326737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326737).length < 2 ^ (prefixWord ++ tailWord_2326737).sum := by decide
  have hdescent : baseEnd_2326737 < baseStart_2326737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326777 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 2, 4, 5]
def baseStart_2326777 : Nat := 118140960795 + 2326777 * 2 ^ 59
def prefixEnd_2326777 : Nat := 4983230072969 + 3 ^ 40 * 2326777 * 2
def baseEnd_2326777 : Nat := 1194754976826548207986853

theorem tailTrace_2326777 : CollatzResearch.WordTrace tailWord_2326777 prefixEnd_2326777 1194754976826548207986853 := by
  unfold tailWord_2326777
  simp only [CollatzResearch.WordTrace]
  refine ⟨84864529091491785719522585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56576352727661190479681723 84864529091491785719522585)
  ·
    refine ⟨63648396818618839289641939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84864529091491785719522585 63648396818618839289641939)
    ·
      refine ⟨95472595227928258934462909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63648396818618839289641939 95472595227928258934462909)
      ·
        refine ⟨35802223210473097100423591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95472595227928258934462909 35802223210473097100423591)
        ·
          refine ⟨53703334815709645650635387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35802223210473097100423591 53703334815709645650635387)
          ·
            refine ⟨80555002223564468475953081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53703334815709645650635387 80555002223564468475953081)
            ·
              refine ⟨60416251667673351356964811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80555002223564468475953081 60416251667673351356964811)
              ·
                refine ⟨90624377501510027035447217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60416251667673351356964811 90624377501510027035447217)
                ·
                  refine ⟨67968283126132520276585413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90624377501510027035447217 67968283126132520276585413)
                  ·
                    refine ⟨12744053086149847551859765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67968283126132520276585413 12744053086149847551859765)
                    ·
                      refine ⟨1194754976826548207986853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12744053086149847551859765 1194754976826548207986853)
                      ·
                        rfl

theorem cell23_2326777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_2326777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326777 prefixEnd_2326777 := by exact prefixLift 2326777
  have htrace : WordTrace (prefixWord ++ tailWord_2326777) baseStart_2326777 baseEnd_2326777 := by
    simpa [prefixWord, tailWord_2326777, baseEnd_2326777] using wordTrace_append hprefix tailTrace_2326777
  have hstable : (prefixWord ++ tailWord_2326777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326777).length < 2 ^ (prefixWord ++ tailWord_2326777).sum := by decide
  have hdescent : baseEnd_2326777 < baseStart_2326777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326784 : List Nat := [2, 1, 1, 2, 1, 1, 4, 5, 1, 5]
def baseStart_2326784 : Nat := 118140960795 + 2326784 * 2 ^ 59
def prefixEnd_2326784 : Nat := 4983230072969 + 3 ^ 40 * 2326784 * 2
def baseEnd_2326784 : Nat := 398252857063709893533107

theorem tailTrace_2326784 : CollatzResearch.WordTrace tailWord_2326784 prefixEnd_2326784 398252857063709893533107 := by
  unfold tailWord_2326784
  simp only [CollatzResearch.WordTrace]
  refine ⟨42432392201233212957513703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56576522934977617276684937 42432392201233212957513703)
  ·
    refine ⟨63648588301849819436270555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42432392201233212957513703 63648588301849819436270555)
    ·
      refine ⟨95472882452774729154405833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63648588301849819436270555 95472882452774729154405833)
      ·
        refine ⟨71604661839581046865804375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95472882452774729154405833 71604661839581046865804375)
        ·
          refine ⟨107406992759371570298706563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71604661839581046865804375 107406992759371570298706563)
          ·
            refine ⟨161110489139057355448059845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107406992759371570298706563 161110489139057355448059845)
            ·
              refine ⟨30208216713573254146511221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 161110489139057355448059845 30208216713573254146511221)
              ·
                refine ⟨2832020316897492576235427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30208216713573254146511221 2832020316897492576235427)
                ·
                  refine ⟨4248030475346238864353141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2832020316897492576235427 4248030475346238864353141)
                  ·
                    refine ⟨398252857063709893533107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4248030475346238864353141 398252857063709893533107)
                    ·
                      rfl

theorem cell23_2326784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 1, 5].length) (baseStart_2326784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326784 prefixEnd_2326784 := by exact prefixLift 2326784
  have htrace : WordTrace (prefixWord ++ tailWord_2326784) baseStart_2326784 baseEnd_2326784 := by
    simpa [prefixWord, tailWord_2326784, baseEnd_2326784] using wordTrace_append hprefix tailTrace_2326784
  have hstable : (prefixWord ++ tailWord_2326784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326784).length < 2 ^ (prefixWord ++ tailWord_2326784).sum := by decide
  have hdescent : baseEnd_2326784 < baseStart_2326784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326855 : List Nat := [1, 1, 4, 1, 2, 2, 1, 6, 1, 2, 2]
def baseStart_2326855 : Nat := 118140960795 + 2326855 * 2 ^ 59
def prefixEnd_2326855 : Nat := 4983230072969 + 3 ^ 40 * 2326855 * 2
def baseEnd_2326855 : Nat := 1194795028317598902811495

theorem tailTrace_2326855 : CollatzResearch.WordTrace tailWord_2326855 prefixEnd_2326855 1194795028317598902811495 := by
  unfold tailWord_2326855
  simp only [CollatzResearch.WordTrace]
  refine ⟨84867373985209205040862019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56578249323472803360574679 84867373985209205040862019)
  ·
    refine ⟨127301060977813807561293029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84867373985209205040862019 127301060977813807561293029)
    ·
      refine ⟨23868948933340088917742443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127301060977813807561293029 23868948933340088917742443)
      ·
        refine ⟨35803423400010133376613665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23868948933340088917742443 35803423400010133376613665)
        ·
          refine ⟨26852567550007600032460249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35803423400010133376613665 26852567550007600032460249)
          ·
            refine ⟨20139425662505700024345187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26852567550007600032460249 20139425662505700024345187)
            ·
              refine ⟨30209138493758550036517781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20139425662505700024345187 30209138493758550036517781)
              ·
                refine ⟨1416053366894932032961771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30209138493758550036517781 1416053366894932032961771)
                ·
                  refine ⟨2124080050342398049442657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1416053366894932032961771 2124080050342398049442657)
                  ·
                    refine ⟨1593060037756798537081993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2124080050342398049442657 1593060037756798537081993)
                    ·
                      refine ⟨1194795028317598902811495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1593060037756798537081993 1194795028317598902811495)
                      ·
                        rfl

theorem cell23_2326855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 6, 1, 2, 2].length) (baseStart_2326855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326855 prefixEnd_2326855 := by exact prefixLift 2326855
  have htrace : WordTrace (prefixWord ++ tailWord_2326855) baseStart_2326855 baseEnd_2326855 := by
    simpa [prefixWord, tailWord_2326855, baseEnd_2326855] using wordTrace_append hprefix tailTrace_2326855
  have hstable : (prefixWord ++ tailWord_2326855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326855).length < 2 ^ (prefixWord ++ tailWord_2326855).sum := by decide
  have hdescent : baseEnd_2326855 < baseStart_2326855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326868 : List Nat := [2, 4, 1, 1, 2, 4, 1, 1, 1, 2, 4]
def baseStart_2326868 : Nat := 118140960795 + 2326868 * 2 ^ 59
def prefixEnd_2326868 : Nat := 4983230072969 + 3 ^ 40 * 2326868 * 2
def baseEnd_2326868 : Nat := 1194801703566107351948935

theorem tailTrace_2326868 : CollatzResearch.WordTrace tailWord_2326868 prefixEnd_2326868 1194801703566107351948935 := by
  unfold tailWord_2326868
  simp only [CollatzResearch.WordTrace]
  refine ⟨42433924067081054130542629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56578565422774738840723505 42433924067081054130542629)
  ·
    refine ⟨7956360762577697649476743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42433924067081054130542629 7956360762577697649476743)
    ·
      refine ⟨11934541143866546474215115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7956360762577697649476743 11934541143866546474215115)
      ·
        refine ⟨17901811715799819711322673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11934541143866546474215115 17901811715799819711322673)
        ·
          refine ⟨13426358786849864783492005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17901811715799819711322673 13426358786849864783492005)
          ·
            refine ⟨2517442272534349646904751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13426358786849864783492005 2517442272534349646904751)
            ·
              refine ⟨3776163408801524470357127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2517442272534349646904751 3776163408801524470357127)
              ·
                refine ⟨5664245113202286705535691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3776163408801524470357127 5664245113202286705535691)
                ·
                  refine ⟨8496367669803430058303537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5664245113202286705535691 8496367669803430058303537)
                  ·
                    refine ⟨6372275752352572543727653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8496367669803430058303537 6372275752352572543727653)
                    ·
                      refine ⟨1194801703566107351948935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6372275752352572543727653 1194801703566107351948935)
                      ·
                        rfl

theorem cell23_2326868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_2326868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326868 prefixEnd_2326868 := by exact prefixLift 2326868
  have htrace : WordTrace (prefixWord ++ tailWord_2326868) baseStart_2326868 baseEnd_2326868 := by
    simpa [prefixWord, tailWord_2326868, baseEnd_2326868] using wordTrace_append hprefix tailTrace_2326868
  have hstable : (prefixWord ++ tailWord_2326868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326868).length < 2 ^ (prefixWord ++ tailWord_2326868).sum := by decide
  have hdescent : baseEnd_2326868 < baseStart_2326868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326884 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 1, 4, 5]
def baseStart_2326884 : Nat := 118140960795 + 2326884 * 2 ^ 59
def prefixEnd_2326884 : Nat := 4983230072969 + 3 ^ 40 * 2326884 * 2
def baseEnd_2326884 : Nat := 1194809919256579289348861

theorem tailTrace_2326884 : CollatzResearch.WordTrace tailWord_2326884 prefixEnd_2326884 1194809919256579289348861 := by
  unfold tailWord_2326884
  simp only [CollatzResearch.WordTrace]
  refine ⟨42434215851052071496833853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56578954468069428662445137 42434215851052071496833853)
  ·
    refine ⟨15912830944144526811312695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42434215851052071496833853 15912830944144526811312695)
    ·
      refine ⟨23869246416216790216969043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15912830944144526811312695 23869246416216790216969043)
      ·
        refine ⟨35803869624325185325453565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23869246416216790216969043 35803869624325185325453565)
        ·
          refine ⟨13426451109121944497045087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35803869624325185325453565 13426451109121944497045087)
          ·
            refine ⟨20139676663682916745567631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13426451109121944497045087 20139676663682916745567631)
            ·
              refine ⟨30209514995524375118351447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20139676663682916745567631 30209514995524375118351447)
              ·
                refine ⟨45314272493286562677527171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30209514995524375118351447 45314272493286562677527171)
                ·
                  refine ⟨67971408739929844016290757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45314272493286562677527171 67971408739929844016290757)
                  ·
                    refine ⟨12744639138736845753054517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67971408739929844016290757 12744639138736845753054517)
                    ·
                      refine ⟨1194809919256579289348861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12744639138736845753054517 1194809919256579289348861)
                      ·
                        rfl

theorem cell23_2326884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_2326884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326884 prefixEnd_2326884 := by exact prefixLift 2326884
  have htrace : WordTrace (prefixWord ++ tailWord_2326884) baseStart_2326884 baseEnd_2326884 := by
    simpa [prefixWord, tailWord_2326884, baseEnd_2326884] using wordTrace_append hprefix tailTrace_2326884
  have hstable : (prefixWord ++ tailWord_2326884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326884).length < 2 ^ (prefixWord ++ tailWord_2326884).sum := by decide
  have hdescent : baseEnd_2326884 < baseStart_2326884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326888 : List Nat := [2, 1, 4, 2, 2, 1, 1, 2, 4, 1, 3]
def baseStart_2326888 : Nat := 118140960795 + 2326888 * 2 ^ 59
def prefixEnd_2326888 : Nat := 4983230072969 + 3 ^ 40 * 2326888 * 2
def baseEnd_2326888 : Nat := 1194811973179197273698843

theorem tailTrace_2326888 : CollatzResearch.WordTrace tailWord_2326888 prefixEnd_2326888 1194811973179197273698843 := by
  unfold tailWord_2326888
  simp only [CollatzResearch.WordTrace]
  refine ⟨42434288797044825838406659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56579051729393101117875545 42434288797044825838406659)
  ·
    refine ⟨63651433195567238757609989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42434288797044825838406659 63651433195567238757609989)
    ·
      refine ⟨11934643724168857267051873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63651433195567238757609989 11934643724168857267051873)
      ·
        refine ⟨8950982793126642950288905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11934643724168857267051873 8950982793126642950288905)
        ·
          refine ⟨6713237094844982212716679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8950982793126642950288905 6713237094844982212716679)
          ·
            refine ⟨10069855642267473319075019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6713237094844982212716679 10069855642267473319075019)
            ·
              refine ⟨15104783463401209978612529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10069855642267473319075019 15104783463401209978612529)
              ·
                refine ⟨11328587597550907483959397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15104783463401209978612529 11328587597550907483959397)
                ·
                  refine ⟨2124110174540795153242387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11328587597550907483959397 2124110174540795153242387)
                  ·
                    refine ⟨3186165261811192729863581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2124110174540795153242387 3186165261811192729863581)
                    ·
                      refine ⟨1194811973179197273698843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3186165261811192729863581 1194811973179197273698843)
                      ·
                        rfl

theorem cell23_2326888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_2326888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326888 prefixEnd_2326888 := by exact prefixLift 2326888
  have htrace : WordTrace (prefixWord ++ tailWord_2326888) baseStart_2326888 baseEnd_2326888 := by
    simpa [prefixWord, tailWord_2326888, baseEnd_2326888] using wordTrace_append hprefix tailTrace_2326888
  have hstable : (prefixWord ++ tailWord_2326888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326888).length < 2 ^ (prefixWord ++ tailWord_2326888).sum := by decide
  have hdescent : baseEnd_2326888 < baseStart_2326888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326911 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 3, 4, 2]
def baseStart_2326911 : Nat := 118140960795 + 2326911 * 2 ^ 59
def prefixEnd_2326911 : Nat := 4983230072969 + 3 ^ 40 * 2326911 * 2
def baseEnd_2326911 : Nat := 1194823783234250683711237

theorem tailTrace_2326911 : CollatzResearch.WordTrace tailWord_2326911 prefixEnd_2326911 1194823783234250683711237 := by
  unfold tailWord_2326911
  simp only [CollatzResearch.WordTrace]
  refine ⟨84869416473006326604900587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56579610982004217736600391 84869416473006326604900587)
  ·
    refine ⟨127304124709509489907350881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84869416473006326604900587 127304124709509489907350881)
    ·
      refine ⟨95478093532132117430513161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127304124709509489907350881 95478093532132117430513161)
      ·
        refine ⟨71608570149099088072884871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95478093532132117430513161 71608570149099088072884871)
        ·
          refine ⟨107412855223648632109327307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71608570149099088072884871 107412855223648632109327307)
          ·
            refine ⟨161119282835472948163990961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107412855223648632109327307 161119282835472948163990961)
            ·
              refine ⟨120839462126604711122993221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161119282835472948163990961 120839462126604711122993221)
              ·
                refine ⟨22657399148738383335561229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120839462126604711122993221 22657399148738383335561229)
                ·
                  refine ⟨8496524680776893750835461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22657399148738383335561229 8496524680776893750835461)
                  ·
                    refine ⟨1593098377645667578281649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8496524680776893750835461 1593098377645667578281649)
                    ·
                      refine ⟨1194823783234250683711237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1593098377645667578281649 1194823783234250683711237)
                      ·
                        rfl

theorem cell23_2326911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 4, 2].length) (baseStart_2326911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326911 prefixEnd_2326911 := by exact prefixLift 2326911
  have htrace : WordTrace (prefixWord ++ tailWord_2326911) baseStart_2326911 baseEnd_2326911 := by
    simpa [prefixWord, tailWord_2326911, baseEnd_2326911] using wordTrace_append hprefix tailTrace_2326911
  have hstable : (prefixWord ++ tailWord_2326911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326911).length < 2 ^ (prefixWord ++ tailWord_2326911).sum := by decide
  have hdescent : baseEnd_2326911 < baseStart_2326911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326922 : List Nat := [3, 1, 2, 5, 1, 1, 1, 3, 2, 1, 3]
def baseStart_2326922 : Nat := 118140960795 + 2326922 * 2 ^ 59
def prefixEnd_2326922 : Nat := 4983230072969 + 3 ^ 40 * 2326922 * 2
def baseEnd_2326922 : Nat := 1194829431521450140673687

theorem tailTrace_2326922 : CollatzResearch.WordTrace tailWord_2326922 prefixEnd_2326922 1194829431521450140673687 := by
  unfold tailWord_2326922
  simp only [CollatzResearch.WordTrace]
  refine ⟨21217454418991618870887755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56579878450644316989034013 21217454418991618870887755)
  ·
    refine ⟨31826181628487428306331633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21217454418991618870887755 31826181628487428306331633)
    ·
      refine ⟨23869636221365571229748725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31826181628487428306331633 23869636221365571229748725)
      ·
        refine ⟨2237778395753022302788943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23869636221365571229748725 2237778395753022302788943)
        ·
          refine ⟨3356667593629533454183415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2237778395753022302788943 3356667593629533454183415)
          ·
            refine ⟨5035001390444300181275123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3356667593629533454183415 5035001390444300181275123)
            ·
              refine ⟨7552502085666450271912685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5035001390444300181275123 7552502085666450271912685)
              ·
                refine ⟨2832188282124918851967257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7552502085666450271912685 2832188282124918851967257)
                ·
                  refine ⟨2124141211593689138975443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2832188282124918851967257 2124141211593689138975443)
                  ·
                    refine ⟨3186211817390533708463165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2124141211593689138975443 3186211817390533708463165)
                    ·
                      refine ⟨1194829431521450140673687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3186211817390533708463165 1194829431521450140673687)
                      ·
                        rfl

theorem cell23_2326922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_2326922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326922 prefixEnd_2326922 := by exact prefixLift 2326922
  have htrace : WordTrace (prefixWord ++ tailWord_2326922) baseStart_2326922 baseEnd_2326922 := by
    simpa [prefixWord, tailWord_2326922, baseEnd_2326922] using wordTrace_append hprefix tailTrace_2326922
  have hstable : (prefixWord ++ tailWord_2326922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326922).length < 2 ^ (prefixWord ++ tailWord_2326922).sum := by decide
  have hdescent : baseEnd_2326922 < baseStart_2326922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2326998 : List Nat := [5, 2, 1, 1, 1, 1, 3, 1, 1, 7]
def baseStart_2326998 : Nat := 118140960795 + 2326998 * 2 ^ 59
def prefixEnd_2326998 : Nat := 4983230072969 + 3 ^ 40 * 2326998 * 2
def baseEnd_2326998 : Nat := 398289485350397281107779

theorem tailTrace_2326998 : CollatzResearch.WordTrace tailWord_2326998 prefixEnd_2326998 398289485350397281107779 := by
  unfold tailWord_2326998
  simp only [CollatzResearch.WordTrace]
  refine ⟨5304536851480696278957353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56581726415794093642211765 5304536851480696278957353)
  ·
    refine ⟨3978402638610522209218015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5304536851480696278957353 3978402638610522209218015)
    ·
      refine ⟨5967603957915783313827023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3978402638610522209218015 5967603957915783313827023)
      ·
        refine ⟨8951405936873674970740535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5967603957915783313827023 8951405936873674970740535)
        ·
          refine ⟨13427108905310512456110803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8951405936873674970740535 13427108905310512456110803)
          ·
            refine ⟨20140663357965768684166205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13427108905310512456110803 20140663357965768684166205)
            ·
              refine ⟨7552748759237163256562327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20140663357965768684166205 7552748759237163256562327)
              ·
                refine ⟨11329123138855744884843491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7552748759237163256562327 11329123138855744884843491)
                ·
                  refine ⟨16993684708283617327265237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11329123138855744884843491 16993684708283617327265237)
                  ·
                    refine ⟨398289485350397281107779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16993684708283617327265237 398289485350397281107779)
                    ·
                      rfl

theorem cell23_2326998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_2326998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2326998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2326998 prefixEnd_2326998 := by exact prefixLift 2326998
  have htrace : WordTrace (prefixWord ++ tailWord_2326998) baseStart_2326998 baseEnd_2326998 := by
    simpa [prefixWord, tailWord_2326998, baseEnd_2326998] using wordTrace_append hprefix tailTrace_2326998
  have hstable : (prefixWord ++ tailWord_2326998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2326998).length < 2 ^ (prefixWord ++ tailWord_2326998).sum := by decide
  have hdescent : baseEnd_2326998 < baseStart_2326998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2326998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327001 : List Nat := [1, 2, 1, 2, 4, 1, 3, 1, 1, 3, 4]
def baseStart_2327001 : Nat := 118140960795 + 2327001 * 2 ^ 59
def prefixEnd_2327001 : Nat := 4983230072969 + 3 ^ 40 * 2327001 * 2
def baseEnd_2327001 : Nat := 1194869996493155331585823

theorem tailTrace_2327001 : CollatzResearch.WordTrace tailWord_2327001 prefixEnd_2327001 1194869996493155331585823 := by
  unfold tailWord_2327001
  simp only [CollatzResearch.WordTrace]
  refine ⟨84872699042680271975676857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56581799361786847983784571 84872699042680271975676857)
  ·
    refine ⟨63654524282010203981757643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84872699042680271975676857 63654524282010203981757643)
    ·
      refine ⟨95481786423015305972636465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63654524282010203981757643 95481786423015305972636465)
      ·
        refine ⟨71611339817261479479477349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95481786423015305972636465 71611339817261479479477349)
        ·
          refine ⟨13427126215736527402402003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71611339817261479479477349 13427126215736527402402003)
          ·
            refine ⟨20140689323604791103603005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13427126215736527402402003 20140689323604791103603005)
            ·
              refine ⟨7552758496351796663851127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20140689323604791103603005 7552758496351796663851127)
              ·
                refine ⟨11329137744527694995776691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7552758496351796663851127 11329137744527694995776691)
                ·
                  refine ⟨16993706616791542493665037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11329137744527694995776691 16993706616791542493665037)
                  ·
                    refine ⟨6372639981296828435124389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16993706616791542493665037 6372639981296828435124389)
                    ·
                      refine ⟨1194869996493155331585823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6372639981296828435124389 1194869996493155331585823)
                      ·
                        rfl

theorem cell23_2327001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_2327001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327001 prefixEnd_2327001 := by exact prefixLift 2327001
  have htrace : WordTrace (prefixWord ++ tailWord_2327001) baseStart_2327001 baseEnd_2327001 := by
    simpa [prefixWord, tailWord_2327001, baseEnd_2327001] using wordTrace_append hprefix tailTrace_2327001
  have hstable : (prefixWord ++ tailWord_2327001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327001).length < 2 ^ (prefixWord ++ tailWord_2327001).sum := by decide
  have hdescent : baseEnd_2327001 < baseStart_2327001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327071 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 5, 5]
def baseStart_2327071 : Nat := 118140960795 + 2327071 * 2 ^ 59
def prefixEnd_2327071 : Nat := 4983230072969 + 3 ^ 40 * 2327071 * 2
def baseEnd_2327071 : Nat := 398301980046323352570167

theorem tailTrace_2327071 : CollatzResearch.WordTrace tailWord_2327071 prefixEnd_2327071 398301980046323352570167 := by
  unfold tailWord_2327071
  simp only [CollatzResearch.WordTrace]
  refine ⟨84875252152426673930725067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56583501434951115953816711 84875252152426673930725067)
  ·
    refine ⟨127312878228640010896087601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84875252152426673930725067 127312878228640010896087601)
    ·
      refine ⟨95484658671480008172065701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127312878228640010896087601 95484658671480008172065701)
      ·
        refine ⟨17903373500902501532262319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95484658671480008172065701 17903373500902501532262319)
        ·
          refine ⟨26855060251353752298393479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17903373500902501532262319 26855060251353752298393479)
          ·
            refine ⟨40282590377030628447590219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26855060251353752298393479 40282590377030628447590219)
            ·
              refine ⟨60423885565545942671385329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40282590377030628447590219 60423885565545942671385329)
              ·
                refine ⟨45317914174159457003538997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60423885565545942671385329 45317914174159457003538997)
                ·
                  refine ⟨4248554453827449094081781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45317914174159457003538997 4248554453827449094081781)
                  ·
                    refine ⟨398301980046323352570167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4248554453827449094081781 398301980046323352570167)
                    ·
                      rfl

theorem cell23_2327071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 5].length) (baseStart_2327071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327071 prefixEnd_2327071 := by exact prefixLift 2327071
  have htrace : WordTrace (prefixWord ++ tailWord_2327071) baseStart_2327071 baseEnd_2327071 := by
    simpa [prefixWord, tailWord_2327071, baseEnd_2327071] using wordTrace_append hprefix tailTrace_2327071
  have hstable : (prefixWord ++ tailWord_2327071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327071).length < 2 ^ (prefixWord ++ tailWord_2327071).sum := by decide
  have hdescent : baseEnd_2327071 < baseStart_2327071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327079 : List Nat := [1, 1, 7, 2, 1, 2, 1, 1, 3, 4]
def baseStart_2327079 : Nat := 118140960795 + 2327079 * 2 ^ 59
def prefixEnd_2327079 : Nat := 4983230072969 + 3 ^ 40 * 2327079 * 2
def baseEnd_2327079 : Nat := 398303349328068675470155

theorem tailTrace_2327079 : CollatzResearch.WordTrace tailWord_2327079 prefixEnd_2327079 398303349328068675470155 := by
  unfold tailWord_2327079
  simp only [CollatzResearch.WordTrace]
  refine ⟨84875543936397691297016291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56583695957598460864677527 84875543936397691297016291)
  ·
    refine ⟨127313315904596536945524437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84875543936397691297016291 127313315904596536945524437)
    ·
      refine ⟨2983905841513981334660729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 127313315904596536945524437 2983905841513981334660729)
      ·
        refine ⟨2237929381135486000995547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2983905841513981334660729 2237929381135486000995547)
        ·
          refine ⟨3356894071703229001493321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2237929381135486000995547 3356894071703229001493321)
          ·
            refine ⟨2517670553777421751119991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3356894071703229001493321 2517670553777421751119991)
            ·
              refine ⟨3776505830666132626679987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2517670553777421751119991 3776505830666132626679987)
              ·
                refine ⟨5664758745999198940019981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3776505830666132626679987 5664758745999198940019981)
                ·
                  refine ⟨2124284529749699602507493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5664758745999198940019981 2124284529749699602507493)
                  ·
                    refine ⟨398303349328068675470155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2124284529749699602507493 398303349328068675470155)
                    ·
                      rfl

theorem cell23_2327079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_2327079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327079 prefixEnd_2327079 := by exact prefixLift 2327079
  have htrace : WordTrace (prefixWord ++ tailWord_2327079) baseStart_2327079 baseEnd_2327079 := by
    simpa [prefixWord, tailWord_2327079, baseEnd_2327079] using wordTrace_append hprefix tailTrace_2327079
  have hstable : (prefixWord ++ tailWord_2327079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327079).length < 2 ^ (prefixWord ++ tailWord_2327079).sum := by decide
  have hdescent : baseEnd_2327079 < baseStart_2327079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327092 : List Nat := [2, 5, 1, 3, 1, 1, 1, 3, 6]
def baseStart_2327092 : Nat := 118140960795 + 2327092 * 2 ^ 59
def prefixEnd_2327092 : Nat := 4983230072969 + 3 ^ 40 * 2327092 * 2
def baseEnd_2327092 : Nat := 132768524803634941727545

theorem tailTrace_2327092 : CollatzResearch.WordTrace tailWord_2327092 prefixEnd_2327092 132768524803634941727545 := by
  unfold tailWord_2327092
  simp only [CollatzResearch.WordTrace]
  refine ⟨42438009042675297258619765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56584012056900396344826353 42438009042675297258619765)
  ·
    refine ⟨3978563347750809117995603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42438009042675297258619765 3978563347750809117995603)
    ·
      refine ⟨5967845021626213676993405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3978563347750809117995603 5967845021626213676993405)
      ·
        refine ⟨2237941883109830128872527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5967845021626213676993405 2237941883109830128872527)
        ·
          refine ⟨3356912824664745193308791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2237941883109830128872527 3356912824664745193308791)
          ·
            refine ⟨5035369236997117789963187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3356912824664745193308791 5035369236997117789963187)
            ·
              refine ⟨7553053855495676684944781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5035369236997117789963187 7553053855495676684944781)
              ·
                refine ⟨2832395195810878756854293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7553053855495676684944781 2832395195810878756854293)
                ·
                  refine ⟨132768524803634941727545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2832395195810878756854293 132768524803634941727545)
                  ·
                    rfl

theorem cell23_2327092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_2327092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327092 prefixEnd_2327092 := by exact prefixLift 2327092
  have htrace : WordTrace (prefixWord ++ tailWord_2327092) baseStart_2327092 baseEnd_2327092 := by
    simpa [prefixWord, tailWord_2327092, baseEnd_2327092] using wordTrace_append hprefix tailTrace_2327092
  have hstable : (prefixWord ++ tailWord_2327092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327092).length < 2 ^ (prefixWord ++ tailWord_2327092).sum := by decide
  have hdescent : baseEnd_2327092 < baseStart_2327092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327105 : List Nat := [1, 2, 5, 1, 1, 2, 3, 2, 1, 5]
def baseStart_2327105 : Nat := 118140960795 + 2327105 * 2 ^ 59
def prefixEnd_2327105 : Nat := 4983230072969 + 3 ^ 40 * 2327105 * 2
def baseEnd_2327105 : Nat := 398307799493740974895115

theorem tailTrace_2327105 : CollatzResearch.WordTrace tailWord_2327105 prefixEnd_2327105 398307799493740974895115 := by
  unfold tailWord_2327105
  simp only [CollatzResearch.WordTrace]
  refine ⟨84876492234303497737462769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56584328156202331824975179 84876492234303497737462769)
  ·
    refine ⟨63657369175727623303097077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84876492234303497737462769 63657369175727623303097077)
    ·
      refine ⟨5967878360224464684665351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63657369175727623303097077 5967878360224464684665351)
      ·
        refine ⟨8951817540336697026998027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5967878360224464684665351 8951817540336697026998027)
        ·
          refine ⟨13427726310505045540497041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8951817540336697026998027 13427726310505045540497041)
          ·
            refine ⟨10070794732878784155372781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13427726310505045540497041 10070794732878784155372781)
            ·
              refine ⟨3776548024829544058264793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10070794732878784155372781 3776548024829544058264793)
              ·
                refine ⟨2832411018622158043698595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3776548024829544058264793 2832411018622158043698595)
                ·
                  refine ⟨4248616527933237065547893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2832411018622158043698595 4248616527933237065547893)
                  ·
                    refine ⟨398307799493740974895115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4248616527933237065547893 398307799493740974895115)
                    ·
                      rfl

theorem cell23_2327105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_2327105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327105 prefixEnd_2327105 := by exact prefixLift 2327105
  have htrace : WordTrace (prefixWord ++ tailWord_2327105) baseStart_2327105 baseEnd_2327105 := by
    simpa [prefixWord, tailWord_2327105, baseEnd_2327105] using wordTrace_append hprefix tailTrace_2327105
  have hstable : (prefixWord ++ tailWord_2327105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327105).length < 2 ^ (prefixWord ++ tailWord_2327105).sum := by decide
  have hdescent : baseEnd_2327105 < baseStart_2327105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327118 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 6, 4]
def baseStart_2327118 : Nat := 118140960795 + 2327118 * 2 ^ 59
def prefixEnd_2327118 : Nat := 4983230072969 + 3 ^ 40 * 2327118 * 2
def baseEnd_2327118 : Nat := 398310024576577124607595

theorem tailTrace_2327118 : CollatzResearch.WordTrace tailWord_2327118 prefixEnd_2327118 398310024576577124607595 := by
  unfold tailWord_2327118
  simp only [CollatzResearch.WordTrace]
  refine ⟨10609620797907050119710751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56584644255504267305124005 10609620797907050119710751)
  ·
    refine ⟨15914431196860575179566127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10609620797907050119710751 15914431196860575179566127)
    ·
      refine ⟨23871646795290862769349191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15914431196860575179566127 23871646795290862769349191)
      ·
        refine ⟨35807470192936294154023787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23871646795290862769349191 35807470192936294154023787)
        ·
          refine ⟨53711205289404441231035681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35807470192936294154023787 53711205289404441231035681)
          ·
            refine ⟨40283403967053330923276761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53711205289404441231035681 40283403967053330923276761)
            ·
              refine ⟨30212552975289998192457571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40283403967053330923276761 30212552975289998192457571)
              ·
                refine ⟨45318829462934997288686357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30212552975289998192457571 45318829462934997288686357)
                ·
                  refine ⟨2124320131075077997907173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45318829462934997288686357 2124320131075077997907173)
                  ·
                    refine ⟨398310024576577124607595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2124320131075077997907173 398310024576577124607595)
                    ·
                      rfl

theorem cell23_2327118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_2327118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327118 prefixEnd_2327118 := by exact prefixLift 2327118
  have htrace : WordTrace (prefixWord ++ tailWord_2327118) baseStart_2327118 baseEnd_2327118 := by
    simpa [prefixWord, tailWord_2327118, baseEnd_2327118] using wordTrace_append hprefix tailTrace_2327118
  have hstable : (prefixWord ++ tailWord_2327118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327118).length < 2 ^ (prefixWord ++ tailWord_2327118).sum := by decide
  have hdescent : baseEnd_2327118 < baseStart_2327118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327128 : List Nat := [2, 1, 2, 2, 1, 2, 5, 1, 1, 1, 5]
def baseStart_2327128 : Nat := 118140960795 + 2327128 * 2 ^ 59
def prefixEnd_2327128 : Nat := 4983230072969 + 3 ^ 40 * 2327128 * 2
def baseEnd_2327128 : Nat := 1194935208536276334697739

theorem tailTrace_2327128 : CollatzResearch.WordTrace tailWord_2327128 prefixEnd_2327128 1194935208536276334697739 := by
  unfold tailWord_2327128
  simp only [CollatzResearch.WordTrace]
  refine ⟨42438665556610086332775019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56584887408813448443700025 42438665556610086332775019)
  ·
    refine ⟨63657998334915129499162529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42438665556610086332775019 63657998334915129499162529)
    ·
      refine ⟨47743498751186347124371897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63657998334915129499162529 47743498751186347124371897)
      ·
        refine ⟨35807624063389760343278923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47743498751186347124371897 35807624063389760343278923)
        ·
          refine ⟨53711436095084640514918385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35807624063389760343278923 53711436095084640514918385)
          ·
            refine ⟨40283577071313480386188789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53711436095084640514918385 40283577071313480386188789)
            ·
              refine ⟨3776585350435638786205199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40283577071313480386188789 3776585350435638786205199)
              ·
                refine ⟨5664878025653458179307799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3776585350435638786205199 5664878025653458179307799)
                ·
                  refine ⟨8497317038480187268961699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5664878025653458179307799 8497317038480187268961699)
                  ·
                    refine ⟨12745975557720280903442549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8497317038480187268961699 12745975557720280903442549)
                    ·
                      refine ⟨1194935208536276334697739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12745975557720280903442549 1194935208536276334697739)
                      ·
                        rfl

theorem cell23_2327128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_2327128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327128 prefixEnd_2327128 := by exact prefixLift 2327128
  have htrace : WordTrace (prefixWord ++ tailWord_2327128) baseStart_2327128 baseEnd_2327128 := by
    simpa [prefixWord, tailWord_2327128, baseEnd_2327128] using wordTrace_append hprefix tailTrace_2327128
  have hstable : (prefixWord ++ tailWord_2327128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327128).length < 2 ^ (prefixWord ++ tailWord_2327128).sum := by decide
  have hdescent : baseEnd_2327128 < baseStart_2327128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327151 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 6]
def baseStart_2327151 : Nat := 118140960795 + 2327151 * 2 ^ 59
def prefixEnd_2327151 : Nat := 4983230072969 + 3 ^ 40 * 2327151 * 2
def baseEnd_2327151 : Nat := 1194947018591329744710133

theorem tailTrace_2327151 : CollatzResearch.WordTrace tailWord_2327151 prefixEnd_2327151 1194947018591329744710133 := by
  unfold tailWord_2327151
  simp only [CollatzResearch.WordTrace]
  refine ⟨84878169992136847593637307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56585446661424565062424871 84878169992136847593637307)
  ·
    refine ⟨127317254988205271390455961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84878169992136847593637307 127317254988205271390455961)
    ·
      refine ⟨95487941241153953542841971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127317254988205271390455961 95487941241153953542841971)
      ·
        refine ⟨143231911861730930314262957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95487941241153953542841971 143231911861730930314262957)
        ·
          refine ⟨53711966948149098867848609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143231911861730930314262957 53711966948149098867848609)
          ·
            refine ⟨40283975211111824150886457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53711966948149098867848609 40283975211111824150886457)
            ·
              refine ⟨30212981408333868113164843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40283975211111824150886457 30212981408333868113164843)
              ·
                refine ⟨45319472112500802169747265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30212981408333868113164843 45319472112500802169747265)
                ·
                  refine ⟨33989604084375601627310449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45319472112500802169747265 33989604084375601627310449)
                  ·
                    refine ⟨25492203063281701220482837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33989604084375601627310449 25492203063281701220482837)
                    ·
                      refine ⟨1194947018591329744710133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25492203063281701220482837 1194947018591329744710133)
                      ·
                        rfl

theorem cell23_2327151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 6].length) (baseStart_2327151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327151 prefixEnd_2327151 := by exact prefixLift 2327151
  have htrace : WordTrace (prefixWord ++ tailWord_2327151) baseStart_2327151 baseEnd_2327151 := by
    simpa [prefixWord, tailWord_2327151, baseEnd_2327151] using wordTrace_append hprefix tailTrace_2327151
  have hstable : (prefixWord ++ tailWord_2327151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327151).length < 2 ^ (prefixWord ++ tailWord_2327151).sum := by decide
  have hdescent : baseEnd_2327151 < baseStart_2327151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327165 : List Nat := [1, 4, 1, 1, 5, 1, 3, 7]
def baseStart_2327165 : Nat := 118140960795 + 2327165 * 2 ^ 59
def prefixEnd_2327165 : Nat := 4983230072969 + 3 ^ 40 * 2327165 * 2
def baseEnd_2327165 : Nat := 44257563234092321849447

theorem tailTrace_2327165 : CollatzResearch.WordTrace tailWord_2327165 prefixEnd_2327165 44257563234092321849447 := by
  unfold tailWord_2327165
  simp only [CollatzResearch.WordTrace]
  refine ⟨84878680614086127984646949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56585787076057418656431299 84878680614086127984646949)
  ·
    refine ⟨15914752615141148997121303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84878680614086127984646949 15914752615141148997121303)
    ·
      refine ⟨23872128922711723495681955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15914752615141148997121303 23872128922711723495681955)
      ·
        refine ⟨35808193384067585243522933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23872128922711723495681955 35808193384067585243522933)
        ·
          refine ⟨3357018129756336116580275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35808193384067585243522933 3357018129756336116580275)
          ·
            refine ⟨5035527194634504174870413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3357018129756336116580275 5035527194634504174870413)
            ·
              refine ⟨1888322697987939065576405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5035527194634504174870413 1888322697987939065576405)
              ·
                refine ⟨44257563234092321849447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1888322697987939065576405 44257563234092321849447)
                ·
                  rfl

theorem cell23_2327165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 7].length) (baseStart_2327165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327165 prefixEnd_2327165 := by exact prefixLift 2327165
  have htrace : WordTrace (prefixWord ++ tailWord_2327165) baseStart_2327165 baseEnd_2327165 := by
    simpa [prefixWord, tailWord_2327165, baseEnd_2327165] using wordTrace_append hprefix tailTrace_2327165
  have hstable : (prefixWord ++ tailWord_2327165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327165).length < 2 ^ (prefixWord ++ tailWord_2327165).sum := by decide
  have hdescent : baseEnd_2327165 < baseStart_2327165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327170 : List Nat := [3, 4, 3, 1, 1, 1, 2, 3, 1, 1, 3]
def baseStart_2327170 : Nat := 118140960795 + 2327170 * 2 ^ 59
def prefixEnd_2327170 : Nat := 4983230072969 + 3 ^ 40 * 2327170 * 2
def baseEnd_2327170 : Nat := 1194956774723765170372547

theorem tailTrace_2327170 : CollatzResearch.WordTrace tailWord_2327170 prefixEnd_2327170 1194956774723765170372547 := by
  unfold tailWord_2327170
  simp only [CollatzResearch.WordTrace]
  refine ⟨21219715744767003459644741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56585908652712009225719309 21219715744767003459644741)
  ·
    refine ⟨3978696702143813148683389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21219715744767003459644741 3978696702143813148683389)
    ·
      refine ⟨1492011263303929930756271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3978696702143813148683389 1492011263303929930756271)
      ·
        refine ⟨2238016894955894896134407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1492011263303929930756271 2238016894955894896134407)
        ·
          refine ⟨3357025342433842344201611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2238016894955894896134407 3357025342433842344201611)
          ·
            refine ⟨5035538013650763516302417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3357025342433842344201611 5035538013650763516302417)
            ·
              refine ⟨3776653510238072637226813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5035538013650763516302417 3776653510238072637226813)
              ·
                refine ⟨1416245066339277238960055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3776653510238072637226813 1416245066339277238960055)
                ·
                  refine ⟨2124367599508915858440083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1416245066339277238960055 2124367599508915858440083)
                  ·
                    refine ⟨3186551399263373787660125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2124367599508915858440083 3186551399263373787660125)
                    ·
                      refine ⟨1194956774723765170372547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3186551399263373787660125 1194956774723765170372547)
                      ·
                        rfl

theorem cell23_2327170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_2327170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327170 prefixEnd_2327170 := by exact prefixLift 2327170
  have htrace : WordTrace (prefixWord ++ tailWord_2327170) baseStart_2327170 baseEnd_2327170 := by
    simpa [prefixWord, tailWord_2327170, baseEnd_2327170] using wordTrace_append hprefix tailTrace_2327170
  have hstable : (prefixWord ++ tailWord_2327170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327170).length < 2 ^ (prefixWord ++ tailWord_2327170).sum := by decide
  have hdescent : baseEnd_2327170 < baseStart_2327170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327175 : List Nat := [1, 1, 4, 2, 1, 2, 2, 2, 4, 1, 3]
def baseStart_2327175 : Nat := 118140960795 + 2327175 * 2 ^ 59
def prefixEnd_2327175 : Nat := 4983230072969 + 3 ^ 40 * 2327175 * 2
def baseEnd_2327175 : Nat := 1194959342127037650810023

theorem tailTrace_2327175 : CollatzResearch.WordTrace tailWord_2327175 prefixEnd_2327175 1194959342127037650810023 := by
  unfold tailWord_2327175
  simp only [CollatzResearch.WordTrace]
  refine ⟨84879045344049899692510979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56586030229366599795007319 84879045344049899692510979)
  ·
    refine ⟨127318568016074849538766469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84879045344049899692510979 127318568016074849538766469)
    ·
      refine ⟨23872231503014034288518713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127318568016074849538766469 23872231503014034288518713)
      ·
        refine ⟨17904173627260525716389035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23872231503014034288518713 17904173627260525716389035)
        ·
          refine ⟨26856260440890788574583553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17904173627260525716389035 26856260440890788574583553)
          ·
            refine ⟨20142195330668091430937665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26856260440890788574583553 20142195330668091430937665)
            ·
              refine ⟨15106646498001068573203249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20142195330668091430937665 15106646498001068573203249)
              ·
                refine ⟨11329984873500801429902437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15106646498001068573203249 11329984873500801429902437)
                ·
                  refine ⟨2124372163781400268106707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11329984873500801429902437 2124372163781400268106707)
                  ·
                    refine ⟨3186558245672100402160061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2124372163781400268106707 3186558245672100402160061)
                    ·
                      refine ⟨1194959342127037650810023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3186558245672100402160061 1194959342127037650810023)
                      ·
                        rfl

theorem cell23_2327175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_2327175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327175 prefixEnd_2327175 := by exact prefixLift 2327175
  have htrace : WordTrace (prefixWord ++ tailWord_2327175) baseStart_2327175 baseEnd_2327175 := by
    simpa [prefixWord, tailWord_2327175, baseEnd_2327175] using wordTrace_append hprefix tailTrace_2327175
  have hstable : (prefixWord ++ tailWord_2327175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327175).length < 2 ^ (prefixWord ++ tailWord_2327175).sum := by decide
  have hdescent : baseEnd_2327175 < baseStart_2327175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327211 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 12]
def baseStart_2327211 : Nat := 118140960795 + 2327211 * 2 ^ 59
def prefixEnd_2327211 : Nat := 4983230072969 + 3 ^ 40 * 2327211 * 2
def baseEnd_2327211 : Nat := 1194977827430599509959857

theorem tailTrace_2327211 : CollatzResearch.WordTrace tailWord_2327211 prefixEnd_2327211 1194977827430599509959857 := by
  unfold tailWord_2327211
  simp only [CollatzResearch.WordTrace]
  refine ⟨84880358371919477840821487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56586905581279651893880991 84880358371919477840821487)
  ·
    refine ⟨127320537557879216761232231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84880358371919477840821487 127320537557879216761232231)
    ·
      refine ⟨190980806336818825141848347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127320537557879216761232231 190980806336818825141848347)
      ·
        refine ⟨286471209505228237712772521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190980806336818825141848347 286471209505228237712772521)
        ·
          refine ⟨214853407128921178284579391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286471209505228237712772521 214853407128921178284579391)
          ·
            refine ⟨322280110693381767426869087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214853407128921178284579391 322280110693381767426869087)
            ·
              refine ⟨483420166040072651140303631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322280110693381767426869087 483420166040072651140303631)
              ·
                refine ⟨725130249060108976710455447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 483420166040072651140303631 725130249060108976710455447)
                ·
                  refine ⟨1087695373590163465065683171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 725130249060108976710455447 1087695373590163465065683171)
                  ·
                    refine ⟨1631543060385245197598524757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1087695373590163465065683171 1631543060385245197598524757)
                    ·
                      refine ⟨1194977827430599509959857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 12 1631543060385245197598524757 1194977827430599509959857)
                      ·
                        rfl

theorem cell23_2327211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 12].length) (baseStart_2327211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327211 prefixEnd_2327211 := by exact prefixLift 2327211
  have htrace : WordTrace (prefixWord ++ tailWord_2327211) baseStart_2327211 baseEnd_2327211 := by
    simpa [prefixWord, tailWord_2327211, baseEnd_2327211] using wordTrace_append hprefix tailTrace_2327211
  have hstable : (prefixWord ++ tailWord_2327211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327211).length < 2 ^ (prefixWord ++ tailWord_2327211).sum := by decide
  have hdescent : baseEnd_2327211 < baseStart_2327211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327218 : List Nat := [3, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5]
def baseStart_2327218 : Nat := 118140960795 + 2327218 * 2 ^ 59
def prefixEnd_2327218 : Nat := 4983230072969 + 3 ^ 40 * 2327218 * 2
def baseEnd_2327218 : Nat := 1194981421795180982572325

theorem tailTrace_2327218 : CollatzResearch.WordTrace tailWord_2327218 prefixEnd_2327218 1194981421795180982572325 := by
  unfold tailWord_2327218
  simp only [CollatzResearch.WordTrace]
  refine ⟨21220153420723529509081577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56587075788596078690884205 21220153420723529509081577)
  ·
    refine ⟨15915115065542647131811183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21220153420723529509081577 15915115065542647131811183)
    ·
      refine ⟨23872672598313970697716775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15915115065542647131811183 23872672598313970697716775)
      ·
        refine ⟨35809008897470956046575163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23872672598313970697716775 35809008897470956046575163)
        ·
          refine ⟨53713513346206434069862745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35809008897470956046575163 53713513346206434069862745)
          ·
            refine ⟨40285135009654825552397059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53713513346206434069862745 40285135009654825552397059)
            ·
              refine ⟨60427702514482238328595589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40285135009654825552397059 60427702514482238328595589)
              ·
                refine ⟨11330194221465419686611673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60427702514482238328595589 11330194221465419686611673)
                ·
                  refine ⟨8497645666099064764958755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11330194221465419686611673 8497645666099064764958755)
                  ·
                    refine ⟨12746468499148597147438133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8497645666099064764958755 12746468499148597147438133)
                    ·
                      refine ⟨1194981421795180982572325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12746468499148597147438133 1194981421795180982572325)
                      ·
                        rfl

theorem cell23_2327218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_2327218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327218 prefixEnd_2327218 := by exact prefixLift 2327218
  have htrace : WordTrace (prefixWord ++ tailWord_2327218) baseStart_2327218 baseEnd_2327218 := by
    simpa [prefixWord, tailWord_2327218, baseEnd_2327218] using wordTrace_append hprefix tailTrace_2327218
  have hstable : (prefixWord ++ tailWord_2327218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327218).length < 2 ^ (prefixWord ++ tailWord_2327218).sum := by decide
  have hdescent : baseEnd_2327218 < baseStart_2327218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327232 : List Nat := [2, 1, 1, 2, 4, 2, 1, 2, 4, 2, 2]
def baseStart_2327232 : Nat := 118140960795 + 2327232 * 2 ^ 59
def prefixEnd_2327232 : Nat := 4983230072969 + 3 ^ 40 * 2327232 * 2
def baseEnd_2327232 : Nat := 1194988610524343927797261

theorem tailTrace_2327232 : CollatzResearch.WordTrace tailWord_2327232 prefixEnd_2327232 1194988610524343927797261 := by
  unfold tailWord_2327232
  simp only [CollatzResearch.WordTrace]
  refine ⟨42440562152421699213667975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56587416203228932284890633 42440562152421699213667975)
  ·
    refine ⟨63660843228632548820501963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42440562152421699213667975 63660843228632548820501963)
    ·
      refine ⟨95491264842948823230752945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63660843228632548820501963 95491264842948823230752945)
      ·
        refine ⟨71618448632211617423064709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95491264842948823230752945 71618448632211617423064709)
        ·
          refine ⟨13428459118539678266824633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71618448632211617423064709 13428459118539678266824633)
          ·
            refine ⟨10071344338904758700118475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13428459118539678266824633 10071344338904758700118475)
            ·
              refine ⟨15107016508357138050177713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10071344338904758700118475 15107016508357138050177713)
              ·
                refine ⟨11330262381267853537633285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15107016508357138050177713 11330262381267853537633285)
                ·
                  refine ⟨2124424196487722538306241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11330262381267853537633285 2124424196487722538306241)
                  ·
                    refine ⟨1593318147365791903729681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2124424196487722538306241 1593318147365791903729681)
                    ·
                      refine ⟨1194988610524343927797261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1593318147365791903729681 1194988610524343927797261)
                      ·
                        rfl

theorem cell23_2327232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 4, 2, 2].length) (baseStart_2327232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327232 prefixEnd_2327232 := by exact prefixLift 2327232
  have htrace : WordTrace (prefixWord ++ tailWord_2327232) baseStart_2327232 baseEnd_2327232 := by
    simpa [prefixWord, tailWord_2327232, baseEnd_2327232] using wordTrace_append hprefix tailTrace_2327232
  have hstable : (prefixWord ++ tailWord_2327232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327232).length < 2 ^ (prefixWord ++ tailWord_2327232).sum := by decide
  have hdescent : baseEnd_2327232 < baseStart_2327232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327255 : List Nat := [1, 1, 3, 2, 1, 6, 1, 1, 7]
def baseStart_2327255 : Nat := 118140960795 + 2327255 * 2 ^ 59
def prefixEnd_2327255 : Nat := 4983230072969 + 3 ^ 40 * 2327255 * 2
def baseEnd_2327255 : Nat := 132777824508821926423295

theorem tailTrace_2327255 : CollatzResearch.WordTrace tailWord_2327255 prefixEnd_2327255 132777824508821926423295 := by
  unfold tailWord_2327255
  simp only [CollatzResearch.WordTrace]
  refine ⟨84881963183760073355423219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56587975455840048903615479 84881963183760073355423219)
  ·
    refine ⟨127322944775640110033134829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84881963183760073355423219 127322944775640110033134829)
    ·
      refine ⟨47746104290865041262425561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127322944775640110033134829 47746104290865041262425561)
      ·
        refine ⟨35809578218148780946819171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47746104290865041262425561 35809578218148780946819171)
        ·
          refine ⟨53714367327223171420228757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35809578218148780946819171 53714367327223171420228757)
          ·
            refine ⟨2517860968463586160323223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 53714367327223171420228757 2517860968463586160323223)
            ·
              refine ⟨3776791452695379240484835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2517860968463586160323223 3776791452695379240484835)
              ·
                refine ⟨5665187179043068860727253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3776791452695379240484835 5665187179043068860727253)
                ·
                  refine ⟨132777824508821926423295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5665187179043068860727253 132777824508821926423295)
                  ·
                    rfl

theorem cell23_2327255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 7].length) (baseStart_2327255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327255 prefixEnd_2327255 := by exact prefixLift 2327255
  have htrace : WordTrace (prefixWord ++ tailWord_2327255) baseStart_2327255 baseEnd_2327255 := by
    simpa [prefixWord, tailWord_2327255, baseEnd_2327255] using wordTrace_append hprefix tailTrace_2327255
  have hstable : (prefixWord ++ tailWord_2327255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327255).length < 2 ^ (prefixWord ++ tailWord_2327255).sum := by decide
  have hdescent : baseEnd_2327255 < baseStart_2327255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327305 : List Nat := [1, 2, 1, 1, 3, 2, 4, 2, 2, 1, 4]
def baseStart_2327305 : Nat := 118140960795 + 2327305 * 2 ^ 59
def prefixEnd_2327305 : Nat := 4983230072969 + 3 ^ 40 * 2327305 * 2
def baseEnd_2327305 : Nat := 1195026094612122142184425

theorem tailTrace_2327305 : CollatzResearch.WordTrace tailWord_2327305 prefixEnd_2327305 1195026094612122142184425 := by
  unfold tailWord_2327305
  simp only [CollatzResearch.WordTrace]
  refine ⟨84883786833578931894743369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56589191222385954596495579 84883786833578931894743369)
  ·
    refine ⟨63662840125184198921057527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84883786833578931894743369 63662840125184198921057527)
    ·
      refine ⟨95494260187776298381586291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63662840125184198921057527 95494260187776298381586291)
      ·
        refine ⟨143241390281664447572379437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95494260187776298381586291 143241390281664447572379437)
        ·
          refine ⟨53715521355624167839642289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143241390281664447572379437 53715521355624167839642289)
          ·
            refine ⟨40286641016718125879731717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53715521355624167839642289 40286641016718125879731717)
            ·
              refine ⟨7553745190634648602449697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40286641016718125879731717 7553745190634648602449697)
              ·
                refine ⟨5665308892975986451837273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7553745190634648602449697 5665308892975986451837273)
                ·
                  refine ⟨4248981669731989838877955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5665308892975986451837273 4248981669731989838877955)
                  ·
                    refine ⟨6373472504597984758316933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4248981669731989838877955 6373472504597984758316933)
                    ·
                      refine ⟨1195026094612122142184425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6373472504597984758316933 1195026094612122142184425)
                      ·
                        rfl

theorem cell23_2327305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 1, 4].length) (baseStart_2327305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327305 prefixEnd_2327305 := by exact prefixLift 2327305
  have htrace : WordTrace (prefixWord ++ tailWord_2327305) baseStart_2327305 baseEnd_2327305 := by
    simpa [prefixWord, tailWord_2327305, baseEnd_2327305] using wordTrace_append hprefix tailTrace_2327305
  have hstable : (prefixWord ++ tailWord_2327305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327305).length < 2 ^ (prefixWord ++ tailWord_2327305).sum := by decide
  have hdescent : baseEnd_2327305 < baseStart_2327305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327308 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 1, 5, 5]
def baseStart_2327308 : Nat := 118140960795 + 2327308 * 2 ^ 59
def prefixEnd_2327308 : Nat := 4983230072969 + 3 ^ 40 * 2327308 * 2
def baseEnd_2327308 : Nat := 1195027635054085630446911

theorem tailTrace_2327308 : CollatzResearch.WordTrace tailWord_2327308 prefixEnd_2327308 1195027635054085630446911 := by
  unfold tailWord_2327308
  simp only [CollatzResearch.WordTrace]
  refine ⟨42441948126284031703551289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56589264168378708938068385 42441948126284031703551289)
  ·
    refine ⟨31831461094713023777663467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42441948126284031703551289 31831461094713023777663467)
    ·
      refine ⟨47747191642069535666495201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31831461094713023777663467 47747191642069535666495201)
      ·
        refine ⟨35810393731552151749871401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47747191642069535666495201 35810393731552151749871401)
        ·
          refine ⟨26857795298664113812403551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35810393731552151749871401 26857795298664113812403551)
          ·
            refine ⟨40286692947996170718605327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26857795298664113812403551 40286692947996170718605327)
            ·
              refine ⟨60430039421994256077907991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40286692947996170718605327 60430039421994256077907991)
              ·
                refine ⟨90645059132991384116861987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60430039421994256077907991 90645059132991384116861987)
                ·
                  refine ⟨135967588699487076175292981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90645059132991384116861987 135967588699487076175292981)
                  ·
                    refine ⟨12746961440576913391433717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 135967588699487076175292981 12746961440576913391433717)
                    ·
                      refine ⟨1195027635054085630446911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12746961440576913391433717 1195027635054085630446911)
                      ·
                        rfl

theorem cell23_2327308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_2327308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327308 prefixEnd_2327308 := by exact prefixLift 2327308
  have htrace : WordTrace (prefixWord ++ tailWord_2327308) baseStart_2327308 baseEnd_2327308 := by
    simpa [prefixWord, tailWord_2327308, baseEnd_2327308] using wordTrace_append hprefix tailTrace_2327308
  have hstable : (prefixWord ++ tailWord_2327308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327308).length < 2 ^ (prefixWord ++ tailWord_2327308).sum := by decide
  have hdescent : baseEnd_2327308 < baseStart_2327308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327315 : List Nat := [1, 1, 1, 2, 1, 3, 4, 3, 3, 4]
def baseStart_2327315 : Nat := 118140960795 + 2327315 * 2 ^ 59
def prefixEnd_2327315 : Nat := 4983230072969 + 3 ^ 40 * 2327315 * 2
def baseEnd_2327315 : Nat := 398343743139555701019793

theorem tailTrace_2327315 : CollatzResearch.WordTrace tailWord_2327315 prefixEnd_2327315 398343743139555701019793 := by
  unfold tailWord_2327315
  simp only [CollatzResearch.WordTrace]
  refine ⟨84884151563542703602607399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56589434375695135735071599 84884151563542703602607399)
  ·
    refine ⟨127326227345314055403911099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84884151563542703602607399 127326227345314055403911099)
    ·
      refine ⟨190989341017971083105866649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127326227345314055403911099 190989341017971083105866649)
      ·
        refine ⟨143242005763478312329399987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190989341017971083105866649 143242005763478312329399987)
        ·
          refine ⟨214863008645217468494099981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143242005763478312329399987 214863008645217468494099981)
          ·
            refine ⟨80573628241956550685287493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 214863008645217468494099981 80573628241956550685287493)
            ·
              refine ⟨15107555295366853253491405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80573628241956550685287493 15107555295366853253491405)
              ·
                refine ⟨5665333235762569970059277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15107555295366853253491405 5665333235762569970059277)
                ·
                  refine ⟨2124499963410963738772229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5665333235762569970059277 2124499963410963738772229)
                  ·
                    refine ⟨398343743139555701019793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2124499963410963738772229 398343743139555701019793)
                    ·
                      rfl

theorem cell23_2327315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 3, 4].length) (baseStart_2327315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327315 prefixEnd_2327315 := by exact prefixLift 2327315
  have htrace : WordTrace (prefixWord ++ tailWord_2327315) baseStart_2327315 baseEnd_2327315 := by
    simpa [prefixWord, tailWord_2327315, baseEnd_2327315] using wordTrace_append hprefix tailTrace_2327315
  have hstable : (prefixWord ++ tailWord_2327315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327315).length < 2 ^ (prefixWord ++ tailWord_2327315).sum := by decide
  have hdescent : baseEnd_2327315 < baseStart_2327315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327322 : List Nat := [3, 1, 1, 3, 2, 1, 3, 1, 2, 4, 2]
def baseStart_2327322 : Nat := 118140960795 + 2327322 * 2 ^ 59
def prefixEnd_2327322 : Nat := 4983230072969 + 3 ^ 40 * 2327322 * 2
def baseEnd_2327322 : Nat := 1195034823783248575671847

theorem tailTrace_2327322 : CollatzResearch.WordTrace tailWord_2327322 prefixEnd_2327322 1195034823783248575671847 := by
  unfold tailWord_2327322
  simp only [CollatzResearch.WordTrace]
  refine ⟨21221101718629335949528055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56589604583011562532074813 21221101718629335949528055)
  ·
    refine ⟨31831652577944003924292083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21221101718629335949528055 31831652577944003924292083)
    ·
      refine ⟨47747478866916005886438125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31831652577944003924292083 47747478866916005886438125)
      ·
        refine ⟨17905304575093502207414297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47747478866916005886438125 17905304575093502207414297)
        ·
          refine ⟨13428978431320126655560723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17905304575093502207414297 13428978431320126655560723)
          ·
            refine ⟨20143467646980189983341085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13428978431320126655560723 20143467646980189983341085)
            ·
              refine ⟨7553800367617571243752907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20143467646980189983341085 7553800367617571243752907)
              ·
                refine ⟨11330700551426356865629361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7553800367617571243752907 11330700551426356865629361)
                ·
                  refine ⟨8498025413569767649222021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11330700551426356865629361 8498025413569767649222021)
                  ·
                    refine ⟨1593379765044331434229129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8498025413569767649222021 1593379765044331434229129)
                    ·
                      refine ⟨1195034823783248575671847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1593379765044331434229129 1195034823783248575671847)
                      ·
                        rfl

theorem cell23_2327322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_2327322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327322 prefixEnd_2327322 := by exact prefixLift 2327322
  have htrace : WordTrace (prefixWord ++ tailWord_2327322) baseStart_2327322 baseEnd_2327322 := by
    simpa [prefixWord, tailWord_2327322, baseEnd_2327322] using wordTrace_append hprefix tailTrace_2327322
  have hstable : (prefixWord ++ tailWord_2327322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327322).length < 2 ^ (prefixWord ++ tailWord_2327322).sum := by decide
  have hdescent : baseEnd_2327322 < baseStart_2327322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327349 : List Nat := [1, 3, 3, 1, 3, 1, 1, 5, 1, 4]
def baseStart_2327349 : Nat := 118140960795 + 2327349 * 2 ^ 59
def prefixEnd_2327349 : Nat := 4983230072969 + 3 ^ 40 * 2327349 * 2
def baseEnd_2327349 : Nat := 398349562586973323344741

theorem tailTrace_2327349 : CollatzResearch.WordTrace tailWord_2327349 prefixEnd_2327349 398349562586973323344741 := by
  unfold tailWord_2327349
  simp only [CollatzResearch.WordTrace]
  refine ⟨84885391645419527409345101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56590261096946351606230067 84885391645419527409345101)
  ·
    refine ⟨31832021867032322778504413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84885391645419527409345101 31832021867032322778504413)
    ·
      refine ⟨11937008200137121041939155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31832021867032322778504413 11937008200137121041939155)
      ·
        refine ⟨17905512300205681562908733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11937008200137121041939155 17905512300205681562908733)
        ·
          refine ⟨6714567112577130586090775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17905512300205681562908733 6714567112577130586090775)
          ·
            refine ⟨10071850668865695879136163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6714567112577130586090775 10071850668865695879136163)
            ·
              refine ⟨15107776003298543818704245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10071850668865695879136163 15107776003298543818704245)
              ·
                refine ⟨1416354000309238483003523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15107776003298543818704245 1416354000309238483003523)
                ·
                  refine ⟨2124531000463857724505285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1416354000309238483003523 2124531000463857724505285)
                  ·
                    refine ⟨398349562586973323344741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2124531000463857724505285 398349562586973323344741)
                    ·
                      rfl

theorem cell23_2327349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_2327349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327349 prefixEnd_2327349 := by exact prefixLift 2327349
  have htrace : WordTrace (prefixWord ++ tailWord_2327349) baseStart_2327349 baseEnd_2327349 := by
    simpa [prefixWord, tailWord_2327349, baseEnd_2327349] using wordTrace_append hprefix tailTrace_2327349
  have hstable : (prefixWord ++ tailWord_2327349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327349).length < 2 ^ (prefixWord ++ tailWord_2327349).sum := by decide
  have hdescent : baseEnd_2327349 < baseStart_2327349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327392 : List Nat := [2, 1, 1, 3, 3, 1, 4, 2, 1, 5]
def baseStart_2327392 : Nat := 118140960795 + 2327392 * 2 ^ 59
def prefixEnd_2327392 : Nat := 4983230072969 + 3 ^ 40 * 2327392 * 2
def baseEnd_2327392 : Nat := 398356922476354433932175

theorem tailTrace_2327392 : CollatzResearch.WordTrace tailWord_2327392 prefixEnd_2327392 398356922476354433932175 := by
  unfold tailWord_2327392
  simp only [CollatzResearch.WordTrace]
  refine ⟨42443479992131872876580215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56591306656175830502106953 42443479992131872876580215)
  ·
    refine ⟨63665219988197809314870323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42443479992131872876580215 63665219988197809314870323)
    ·
      refine ⟨95497829982296713972305485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63665219988197809314870323 95497829982296713972305485)
      ·
        refine ⟨35811686243361267739614557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95497829982296713972305485 35811686243361267739614557)
        ·
          refine ⟨13429382341260475402355459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35811686243361267739614557 13429382341260475402355459)
          ·
            refine ⟨20144073511890713103533189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13429382341260475402355459 20144073511890713103533189)
            ·
              refine ⟨3777013783479508706912473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20144073511890713103533189 3777013783479508706912473)
              ·
                refine ⟨2832760337609631530184355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3777013783479508706912473 2832760337609631530184355)
                ·
                  refine ⟨4249140506414447295276533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2832760337609631530184355 4249140506414447295276533)
                  ·
                    refine ⟨398356922476354433932175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4249140506414447295276533 398356922476354433932175)
                    ·
                      rfl

theorem cell23_2327392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 1, 5].length) (baseStart_2327392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327392 prefixEnd_2327392 := by exact prefixLift 2327392
  have htrace : WordTrace (prefixWord ++ tailWord_2327392) baseStart_2327392 baseEnd_2327392 := by
    simpa [prefixWord, tailWord_2327392, baseEnd_2327392] using wordTrace_append hprefix tailTrace_2327392
  have hstable : (prefixWord ++ tailWord_2327392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327392).length < 2 ^ (prefixWord ++ tailWord_2327392).sum := by decide
  have hdescent : baseEnd_2327392 < baseStart_2327392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327405 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 3, 6]
def baseStart_2327405 : Nat := 118140960795 + 2327405 * 2 ^ 59
def prefixEnd_2327405 : Nat := 4983230072969 + 3 ^ 40 * 2327405 * 2
def baseEnd_2327405 : Nat := 398359147559190583644655

theorem tailTrace_2327405 : CollatzResearch.WordTrace tailWord_2327405 prefixEnd_2327405 398359147559190583644655 := by
  unfold tailWord_2327405
  simp only [CollatzResearch.WordTrace]
  refine ⟨84887434133216648973383669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56591622755477765982255779 84887434133216648973383669)
  ·
    refine ⟨7958196949989060841254719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84887434133216648973383669 7958196949989060841254719)
    ·
      refine ⟨11937295424983591261882079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7958196949989060841254719 11937295424983591261882079)
      ·
        refine ⟨17905943137475386892823119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11937295424983591261882079 17905943137475386892823119)
        ·
          refine ⟨26858914706213080339234679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17905943137475386892823119 26858914706213080339234679)
          ·
            refine ⟨40288372059319620508852019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26858914706213080339234679 40288372059319620508852019)
            ·
              refine ⟨60432558088979430763278029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40288372059319620508852019 60432558088979430763278029)
              ·
                refine ⟨22662209283367286536229261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60432558088979430763278029 22662209283367286536229261)
                ·
                  refine ⟨8498328481262732451085973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22662209283367286536229261 8498328481262732451085973)
                  ·
                    refine ⟨398359147559190583644655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8498328481262732451085973 398359147559190583644655)
                    ·
                      rfl

theorem cell23_2327405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_2327405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327405 prefixEnd_2327405 := by exact prefixLift 2327405
  have htrace : WordTrace (prefixWord ++ tailWord_2327405) baseStart_2327405 baseEnd_2327405 := by
    simpa [prefixWord, tailWord_2327405, baseEnd_2327405] using wordTrace_append hprefix tailTrace_2327405
  have hstable : (prefixWord ++ tailWord_2327405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327405).length < 2 ^ (prefixWord ++ tailWord_2327405).sum := by decide
  have hdescent : baseEnd_2327405 < baseStart_2327405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327432 : List Nat := [2, 1, 3, 3, 2, 1, 2, 2, 1, 1, 5]
def baseStart_2327432 : Nat := 118140960795 + 2327432 * 2 ^ 59
def prefixEnd_2327432 : Nat := 4983230072969 + 3 ^ 40 * 2327432 * 2
def baseEnd_2327432 : Nat := 1195091306655243145296341

theorem tailTrace_2327432 : CollatzResearch.WordTrace tailWord_2327432 prefixEnd_2327432 1195091306655243145296341 := by
  unfold tailWord_2327432
  simp only [CollatzResearch.WordTrace]
  refine ⟨42444209452059416292308275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56592279269412555056411033 42444209452059416292308275)
  ·
    refine ⟨63666314178089124438462413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42444209452059416292308275 63666314178089124438462413)
    ·
      refine ⟨23874867816783421664423405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63666314178089124438462413 23874867816783421664423405)
      ·
        refine ⟨8953075431293783124158777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23874867816783421664423405 8953075431293783124158777)
        ·
          refine ⟨6714806573470337343119083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8953075431293783124158777 6714806573470337343119083)
          ·
            refine ⟨10072209860205506014678625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6714806573470337343119083 10072209860205506014678625)
            ·
              refine ⟨7554157395154129511008969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10072209860205506014678625 7554157395154129511008969)
              ·
                refine ⟨5665618046365597133256727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7554157395154129511008969 5665618046365597133256727)
                ·
                  refine ⟨8498427069548395699885091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5665618046365597133256727 8498427069548395699885091)
                  ·
                    refine ⟨12747640604322593549827637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8498427069548395699885091 12747640604322593549827637)
                    ·
                      refine ⟨1195091306655243145296341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12747640604322593549827637 1195091306655243145296341)
                      ·
                        rfl

theorem cell23_2327432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_2327432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327432 prefixEnd_2327432 := by exact prefixLift 2327432
  have htrace : WordTrace (prefixWord ++ tailWord_2327432) baseStart_2327432 baseEnd_2327432 := by
    simpa [prefixWord, tailWord_2327432, baseEnd_2327432] using wordTrace_append hprefix tailTrace_2327432
  have hstable : (prefixWord ++ tailWord_2327432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327432).length < 2 ^ (prefixWord ++ tailWord_2327432).sum := by decide
  have hdescent : baseEnd_2327432 < baseStart_2327432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327469 : List Nat := [1, 5, 2, 3, 2, 10]
def baseStart_2327469 : Nat := 118140960795 + 2327469 * 2 ^ 59
def prefixEnd_2327469 : Nat := 4983230072969 + 3 ^ 40 * 2327469 * 2
def baseEnd_2327469 : Nat := 4918149405100656380797

theorem tailTrace_2327469 : CollatzResearch.WordTrace tailWord_2327469 prefixEnd_2327469 4918149405100656380797 := by
  unfold tailWord_2327469
  simp only [CollatzResearch.WordTrace]
  refine ⟨84889768404984787903713461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56593178936656525269142307 84889768404984787903713461)
  ·
    refine ⟨7958415787967323865973137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84889768404984787903713461 7958415787967323865973137)
    ·
      refine ⟨5968811840975492899479853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7958415787967323865973137 5968811840975492899479853)
      ·
        refine ⟨2238304440365809837304945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5968811840975492899479853 2238304440365809837304945)
        ·
          refine ⟨1678728330274357377978709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2238304440365809837304945 1678728330274357377978709)
          ·
            refine ⟨4918149405100656380797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1678728330274357377978709 4918149405100656380797)
            ·
              rfl

theorem cell23_2327469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 10].length) (baseStart_2327469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327469 prefixEnd_2327469 := by exact prefixLift 2327469
  have htrace : WordTrace (prefixWord ++ tailWord_2327469) baseStart_2327469 baseEnd_2327469 := by
    simpa [prefixWord, tailWord_2327469, baseEnd_2327469] using wordTrace_append hprefix tailTrace_2327469
  have hstable : (prefixWord ++ tailWord_2327469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327469).length < 2 ^ (prefixWord ++ tailWord_2327469).sum := by decide
  have hdescent : baseEnd_2327469 < baseStart_2327469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327479 : List Nat := [1, 1, 3, 1, 3, 1, 3, 4, 2, 1, 3]
def baseStart_2327479 : Nat := 118140960795 + 2327479 * 2 ^ 59
def prefixEnd_2327479 : Nat := 4983230072969 + 3 ^ 40 * 2327479 * 2
def baseEnd_2327479 : Nat := 1195115440246004461408625

theorem tailTrace_2327479 : CollatzResearch.WordTrace tailWord_2327479 prefixEnd_2327479 1195115440246004461408625 := by
  unfold tailWord_2327479
  simp only [CollatzResearch.WordTrace]
  refine ⟨84890133134948559611577491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56593422089965706407718327 84890133134948559611577491)
  ·
    refine ⟨127335199702422839417366237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84890133134948559611577491 127335199702422839417366237)
    ·
      refine ⟨47750699888408564781512339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127335199702422839417366237 47750699888408564781512339)
      ·
        refine ⟨71626049832612847172268509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47750699888408564781512339 71626049832612847172268509)
        ·
          refine ⟨26859768687229817689600691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71626049832612847172268509 26859768687229817689600691)
          ·
            refine ⟨40289653030844726534401037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26859768687229817689600691 40289653030844726534401037)
            ·
              refine ⟨15108619886566772450400389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40289653030844726534401037 15108619886566772450400389)
              ·
                refine ⟨2832866228731269834450073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15108619886566772450400389 2832866228731269834450073)
                ·
                  refine ⟨2124649671548452375837555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2832866228731269834450073 2124649671548452375837555)
                  ·
                    refine ⟨3186974507322678563756333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2124649671548452375837555 3186974507322678563756333)
                    ·
                      refine ⟨1195115440246004461408625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3186974507322678563756333 1195115440246004461408625)
                      ·
                        rfl

theorem cell23_2327479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 2, 1, 3].length) (baseStart_2327479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327479 prefixEnd_2327479 := by exact prefixLift 2327479
  have htrace : WordTrace (prefixWord ++ tailWord_2327479) baseStart_2327479 baseEnd_2327479 := by
    simpa [prefixWord, tailWord_2327479, baseEnd_2327479] using wordTrace_append hprefix tailTrace_2327479
  have hstable : (prefixWord ++ tailWord_2327479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327479).length < 2 ^ (prefixWord ++ tailWord_2327479).sum := by decide
  have hdescent : baseEnd_2327479 < baseStart_2327479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327480 : List Nat := [2, 1, 2, 1, 2, 6, 2, 2, 1, 2, 2]
def baseStart_2327480 : Nat := 118140960795 + 2327480 * 2 ^ 59
def prefixEnd_2327480 : Nat := 4983230072969 + 3 ^ 40 * 2327480 * 2
def baseEnd_2327480 : Nat := 1195115953726658957496121

theorem tailTrace_2327480 : CollatzResearch.WordTrace tailWord_2327480 prefixEnd_2327480 1195115953726658957496121 := by
  unfold tailWord_2327480
  simp only [CollatzResearch.WordTrace]
  refine ⟨42445084803972468391181947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56593446405296624521575929 42445084803972468391181947)
  ·
    refine ⟨63667627205958702586772921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42445084803972468391181947 63667627205958702586772921)
    ·
      refine ⟨47750720404469026940079691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63667627205958702586772921 47750720404469026940079691)
      ·
        refine ⟨71626080606703540410119537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47750720404469026940079691 71626080606703540410119537)
        ·
          refine ⟨53719560455027655307589653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71626080606703540410119537 53719560455027655307589653)
          ·
            refine ⟨2518104396329421342543265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 53719560455027655307589653 2518104396329421342543265)
            ·
              refine ⟨1888578297247066006907449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2518104396329421342543265 1888578297247066006907449)
              ·
                refine ⟨1416433722935299505180587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1888578297247066006907449 1416433722935299505180587)
                ·
                  refine ⟨2124650584402949257770881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1416433722935299505180587 2124650584402949257770881)
                  ·
                    refine ⟨1593487938302211943328161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2124650584402949257770881 1593487938302211943328161)
                    ·
                      refine ⟨1195115953726658957496121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1593487938302211943328161 1195115953726658957496121)
                      ·
                        rfl

theorem cell23_2327480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 2, 1, 2, 2].length) (baseStart_2327480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327480 prefixEnd_2327480 := by exact prefixLift 2327480
  have htrace : WordTrace (prefixWord ++ tailWord_2327480) baseStart_2327480 baseEnd_2327480 := by
    simpa [prefixWord, tailWord_2327480, baseEnd_2327480] using wordTrace_append hprefix tailTrace_2327480
  have hstable : (prefixWord ++ tailWord_2327480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327480).length < 2 ^ (prefixWord ++ tailWord_2327480).sum := by decide
  have hdescent : baseEnd_2327480 < baseStart_2327480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327495 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 1, 8]
def baseStart_2327495 : Nat := 118140960795 + 2327495 * 2 ^ 59
def prefixEnd_2327495 : Nat := 4983230072969 + 3 ^ 40 * 2327495 * 2
def baseEnd_2327495 : Nat := 398374551978825466269517

theorem tailTrace_2327495 : CollatzResearch.WordTrace tailWord_2327495 prefixEnd_2327495 398374551978825466269517 := by
  unfold tailWord_2327495
  simp only [CollatzResearch.WordTrace]
  refine ⟨84890716702890594344159939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56593811135260396229439959 84890716702890594344159939)
  ·
    refine ⟨127336075054335891516239909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84890716702890594344159939 127336075054335891516239909)
    ·
      refine ⟨23875514072687979659294983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127336075054335891516239909 23875514072687979659294983)
      ·
        refine ⟨35813271109031969488942475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23875514072687979659294983 35813271109031969488942475)
        ·
          refine ⟨53719906663547954233413713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35813271109031969488942475 53719906663547954233413713)
          ·
            refine ⟨40289929997660965675060285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53719906663547954233413713 40289929997660965675060285)
            ·
              refine ⟨15108723749122862128147607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40289929997660965675060285 15108723749122862128147607)
              ·
                refine ⟨22663085623684293192221411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15108723749122862128147607 22663085623684293192221411)
                ·
                  refine ⟨33994628435526439788332117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22663085623684293192221411 33994628435526439788332117)
                  ·
                    refine ⟨398374551978825466269517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33994628435526439788332117 398374551978825466269517)
                    ·
                      rfl

theorem cell23_2327495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_2327495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327495 prefixEnd_2327495 := by exact prefixLift 2327495
  have htrace : WordTrace (prefixWord ++ tailWord_2327495) baseStart_2327495 baseEnd_2327495 := by
    simpa [prefixWord, tailWord_2327495, baseEnd_2327495] using wordTrace_append hprefix tailTrace_2327495
  have hstable : (prefixWord ++ tailWord_2327495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327495).length < 2 ^ (prefixWord ++ tailWord_2327495).sum := by decide
  have hdescent : baseEnd_2327495 < baseStart_2327495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327506 : List Nat := [3, 2, 2, 3, 1, 1, 2, 1, 3, 3, 2]
def baseStart_2327506 : Nat := 118140960795 + 2327506 * 2 ^ 59
def prefixEnd_2327506 : Nat := 4983230072969 + 3 ^ 40 * 2327506 * 2
def baseEnd_2327506 : Nat := 1195129304223675855771001

theorem tailTrace_2327506 : CollatzResearch.WordTrace tailWord_2327506 prefixEnd_2327506 1195129304223675855771001 := by
  unfold tailWord_2327506
  simp only [CollatzResearch.WordTrace]
  refine ⟨21222779476462685805702593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56594078603900495481873581 21222779476462685805702593)
  ·
    refine ⟨15917084607347014354276945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21222779476462685805702593 15917084607347014354276945)
    ·
      refine ⟨11937813455510260765707709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15917084607347014354276945 11937813455510260765707709)
      ·
        refine ⟨4476680045816347787140391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11937813455510260765707709 4476680045816347787140391)
        ·
          refine ⟨6715020068724521680710587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4476680045816347787140391 6715020068724521680710587)
          ·
            refine ⟨10072530103086782521065881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6715020068724521680710587 10072530103086782521065881)
            ·
              refine ⟨7554397577315086890799411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10072530103086782521065881 7554397577315086890799411)
              ·
                refine ⟨11331596365972630336199117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7554397577315086890799411 11331596365972630336199117)
                ·
                  refine ⟨4249348637239736376074669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11331596365972630336199117 4249348637239736376074669)
                  ·
                    refine ⟨1593505738964901141028001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4249348637239736376074669 1593505738964901141028001)
                    ·
                      refine ⟨1195129304223675855771001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1593505738964901141028001 1195129304223675855771001)
                      ·
                        rfl

theorem cell23_2327506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_2327506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327506 prefixEnd_2327506 := by exact prefixLift 2327506
  have htrace : WordTrace (prefixWord ++ tailWord_2327506) baseStart_2327506 baseEnd_2327506 := by
    simpa [prefixWord, tailWord_2327506, baseEnd_2327506] using wordTrace_append hprefix tailTrace_2327506
  have hstable : (prefixWord ++ tailWord_2327506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327506).length < 2 ^ (prefixWord ++ tailWord_2327506).sum := by decide
  have hdescent : baseEnd_2327506 < baseStart_2327506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327576 : List Nat := [2, 1, 2, 3, 2, 4, 1, 3, 5]
def baseStart_2327576 : Nat := 118140960795 + 2327576 * 2 ^ 59
def prefixEnd_2327576 : Nat := 4983230072969 + 3 ^ 40 * 2327576 * 2
def baseEnd_2327576 : Nat := 132796138652165620210631

theorem tailTrace_2327576 : CollatzResearch.WordTrace tailWord_2327576 prefixEnd_2327576 132796138652165620210631 := by
  unfold tailWord_2327576
  simp only [CollatzResearch.WordTrace]
  refine ⟨42446835507798572588929291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56595780677064763451905721 42446835507798572588929291)
  ·
    refine ⟨63670253261697858883393937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42446835507798572588929291 63670253261697858883393937)
    ·
      refine ⟨47752689946273394162545453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63670253261697858883393937 47752689946273394162545453)
      ·
        refine ⟨17907258729852522810954545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47752689946273394162545453 17907258729852522810954545)
        ·
          refine ⟨13430444047389392108215909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17907258729852522810954545 13430444047389392108215909)
          ·
            refine ⟨2518208258885511020290483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13430444047389392108215909 2518208258885511020290483)
            ·
              refine ⟨3777312388328266530435725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2518208258885511020290483 3777312388328266530435725)
              ·
                refine ⟨1416492145623099948913397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3777312388328266530435725 1416492145623099948913397)
                ·
                  refine ⟨132796138652165620210631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1416492145623099948913397 132796138652165620210631)
                  ·
                    rfl

theorem cell23_2327576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 3, 5].length) (baseStart_2327576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327576 prefixEnd_2327576 := by exact prefixLift 2327576
  have htrace : WordTrace (prefixWord ++ tailWord_2327576) baseStart_2327576 baseEnd_2327576 := by
    simpa [prefixWord, tailWord_2327576, baseEnd_2327576] using wordTrace_append hprefix tailTrace_2327576
  have hstable : (prefixWord ++ tailWord_2327576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327576).length < 2 ^ (prefixWord ++ tailWord_2327576).sum := by decide
  have hdescent : baseEnd_2327576 < baseStart_2327576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327652 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 1, 2, 6]
def baseStart_2327652 : Nat := 118140960795 + 2327652 * 2 ^ 59
def prefixEnd_2327652 : Nat := 4983230072969 + 3 ^ 40 * 2327652 * 2
def baseEnd_2327652 : Nat := 1195204272399232284545329

theorem tailTrace_2327652 : CollatzResearch.WordTrace tailWord_2327652 prefixEnd_2327652 1195204272399232284545329 := by
  unfold tailWord_2327652
  simp only [CollatzResearch.WordTrace]
  refine ⟨42448221481660905078812605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56597628642214540105083473 42448221481660905078812605)
  ·
    refine ⟨15918083055622839404554727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42448221481660905078812605 15918083055622839404554727)
    ·
      refine ⟨23877124583434259106832091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15918083055622839404554727 23877124583434259106832091)
      ·
        refine ⟨35815686875151388660248137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23877124583434259106832091 35815686875151388660248137)
        ·
          refine ⟨26861765156363541495186103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35815686875151388660248137 26861765156363541495186103)
          ·
            refine ⟨40292647734545312242779155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26861765156363541495186103 40292647734545312242779155)
            ·
              refine ⟨60438971601817968364168733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40292647734545312242779155 60438971601817968364168733)
              ·
                refine ⟨22664614350681738136563275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60438971601817968364168733 22664614350681738136563275)
                ·
                  refine ⟨33996921526022607204844913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22664614350681738136563275 33996921526022607204844913)
                  ·
                    refine ⟨25497691144516955403633685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33996921526022607204844913 25497691144516955403633685)
                    ·
                      refine ⟨1195204272399232284545329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25497691144516955403633685 1195204272399232284545329)
                      ·
                        rfl

theorem cell23_2327652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_2327652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327652 prefixEnd_2327652 := by exact prefixLift 2327652
  have htrace : WordTrace (prefixWord ++ tailWord_2327652) baseStart_2327652 baseEnd_2327652 := by
    simpa [prefixWord, tailWord_2327652, baseEnd_2327652] using wordTrace_append hprefix tailTrace_2327652
  have hstable : (prefixWord ++ tailWord_2327652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327652).length < 2 ^ (prefixWord ++ tailWord_2327652).sum := by decide
  have hdescent : baseEnd_2327652 < baseStart_2327652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327659 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 9, 1, 3]
def baseStart_2327659 : Nat := 118140960795 + 2327659 * 2 ^ 59
def prefixEnd_2327659 : Nat := 4983230072969 + 3 ^ 40 * 2327659 * 2
def baseEnd_2327659 : Nat := 1195207866763813757157797

theorem tailTrace_2327659 : CollatzResearch.WordTrace tailWord_2327659 prefixEnd_2327659 1195207866763813757157797 := by
  unfold tailWord_2327659
  simp only [CollatzResearch.WordTrace]
  refine ⟨84896698274296450353130031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56597798849530966902086687 84896698274296450353130031)
  ·
    refine ⟨127345047411444675529695047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84896698274296450353130031 127345047411444675529695047)
    ·
      refine ⟨191017571117167013294542571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127345047411444675529695047 191017571117167013294542571)
      ·
        refine ⟨286526356675750519941813857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191017571117167013294542571 286526356675750519941813857)
        ·
          refine ⟨214894767506812889956360393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286526356675750519941813857 214894767506812889956360393)
          ·
            refine ⟨161171075630109667467270295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214894767506812889956360393 161171075630109667467270295)
            ·
              refine ⟨241756613445164501200905443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161171075630109667467270295 241756613445164501200905443)
              ·
                refine ⟨362634920167746751801358165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 241756613445164501200905443 362634920167746751801358165)
                ·
                  refine ⟨2124813985357891123836083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 362634920167746751801358165 2124813985357891123836083)
                  ·
                    refine ⟨3187220978036836685754125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2124813985357891123836083 3187220978036836685754125)
                    ·
                      refine ⟨1195207866763813757157797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3187220978036836685754125 1195207866763813757157797)
                      ·
                        rfl

theorem cell23_2327659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 9, 1, 3].length) (baseStart_2327659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327659 prefixEnd_2327659 := by exact prefixLift 2327659
  have htrace : WordTrace (prefixWord ++ tailWord_2327659) baseStart_2327659 baseEnd_2327659 := by
    simpa [prefixWord, tailWord_2327659, baseEnd_2327659] using wordTrace_append hprefix tailTrace_2327659
  have hstable : (prefixWord ++ tailWord_2327659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327659).length < 2 ^ (prefixWord ++ tailWord_2327659).sum := by decide
  have hdescent : baseEnd_2327659 < baseStart_2327659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327676 : List Nat := [2, 2, 2, 1, 1, 3, 3, 2, 3, 1, 3]
def baseStart_2327676 : Nat := 118140960795 + 2327676 * 2 ^ 59
def prefixEnd_2327676 : Nat := 4983230072969 + 3 ^ 40 * 2327676 * 2
def baseEnd_2327676 : Nat := 1195216595934940190645219

theorem tailTrace_2327676 : CollatzResearch.WordTrace tailWord_2327676 prefixEnd_2327676 1195216595934940190645219 := by
  unfold tailWord_2327676
  simp only [CollatzResearch.WordTrace]
  refine ⟨42448659157617431128249441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56598212210156574837665921 42448659157617431128249441)
  ·
    refine ⟨31836494368213073346187081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42448659157617431128249441 31836494368213073346187081)
    ·
      refine ⟨23877370776159805009640311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31836494368213073346187081 23877370776159805009640311)
      ·
        refine ⟨35816056164239707514460467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23877370776159805009640311 35816056164239707514460467)
        ·
          refine ⟨53724084246359561271690701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35816056164239707514460467 53724084246359561271690701)
          ·
            refine ⟨20146531592384835476884013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53724084246359561271690701 20146531592384835476884013)
            ·
              refine ⟨7554949347144313303831505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20146531592384835476884013 7554949347144313303831505)
              ·
                refine ⟨5666212010358234977873629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7554949347144313303831505 5666212010358234977873629)
                ·
                  refine ⟨2124829503884338116702611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5666212010358234977873629 2124829503884338116702611)
                  ·
                    refine ⟨3187244255826507175053917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2124829503884338116702611 3187244255826507175053917)
                    ·
                      refine ⟨1195216595934940190645219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3187244255826507175053917 1195216595934940190645219)
                      ·
                        rfl

theorem cell23_2327676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 3, 1, 3].length) (baseStart_2327676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327676 prefixEnd_2327676 := by exact prefixLift 2327676
  have htrace : WordTrace (prefixWord ++ tailWord_2327676) baseStart_2327676 baseEnd_2327676 := by
    simpa [prefixWord, tailWord_2327676, baseEnd_2327676] using wordTrace_append hprefix tailTrace_2327676
  have hstable : (prefixWord ++ tailWord_2327676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327676).length < 2 ^ (prefixWord ++ tailWord_2327676).sum := by decide
  have hdescent : baseEnd_2327676 < baseStart_2327676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327710 : List Nat := [4, 3, 1, 1, 2, 2, 2, 1, 3, 1, 3]
def baseStart_2327710 : Nat := 118140960795 + 2327710 * 2 ^ 59
def prefixEnd_2327710 : Nat := 4983230072969 + 3 ^ 40 * 2327710 * 2
def baseEnd_2327710 : Nat := 1195234054277193057620063

theorem tailTrace_2327710 : CollatzResearch.WordTrace tailWord_2327710 prefixEnd_2327710 1195234054277193057620063 := by
  unfold tailWord_2327710
  simp only [CollatzResearch.WordTrace]
  refine ⟨10612319799638960757904573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56599038931407790708824389 10612319799638960757904573)
  ·
    refine ⟨3979619924864610284214215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10612319799638960757904573 3979619924864610284214215)
    ·
      refine ⟨5969429887296915426321323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3979619924864610284214215 5969429887296915426321323)
      ·
        refine ⟨8954144830945373139481985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5969429887296915426321323 8954144830945373139481985)
        ·
          refine ⟨6715608623209029854611489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8954144830945373139481985 6715608623209029854611489)
          ·
            refine ⟨5036706467406772390958617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6715608623209029854611489 5036706467406772390958617)
            ·
              refine ⟨3777529850555079293218963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5036706467406772390958617 3777529850555079293218963)
              ·
                refine ⟨5666294775832618939828445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3777529850555079293218963 5666294775832618939828445)
                ·
                  refine ⟨2124860540937232102435667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5666294775832618939828445 2124860540937232102435667)
                  ·
                    refine ⟨3187290811405848153653501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2124860540937232102435667 3187290811405848153653501)
                    ·
                      refine ⟨1195234054277193057620063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3187290811405848153653501 1195234054277193057620063)
                      ·
                        rfl

theorem cell23_2327710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_2327710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327710 prefixEnd_2327710 := by exact prefixLift 2327710
  have htrace : WordTrace (prefixWord ++ tailWord_2327710) baseStart_2327710 baseEnd_2327710 := by
    simpa [prefixWord, tailWord_2327710, baseEnd_2327710] using wordTrace_append hprefix tailTrace_2327710
  have hstable : (prefixWord ++ tailWord_2327710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327710).length < 2 ^ (prefixWord ++ tailWord_2327710).sum := by decide
  have hdescent : baseEnd_2327710 < baseStart_2327710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327749 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 3, 3, 3]
def baseStart_2327749 : Nat := 118140960795 + 2327749 * 2 ^ 59
def prefixEnd_2327749 : Nat := 4983230072969 + 3 ^ 40 * 2327749 * 2
def baseEnd_2327749 : Nat := 1195254080022718405032383

theorem tailTrace_2327749 : CollatzResearch.WordTrace tailWord_2327749 prefixEnd_2327749 1195254080022718405032383 := by
  unfold tailWord_2327749
  simp only [CollatzResearch.WordTrace]
  refine ⟨84899980843970395723906301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56599987229313597149270867 84899980843970395723906301)
  ·
    refine ⟨31837492816488898396464863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84899980843970395723906301 31837492816488898396464863)
    ·
      refine ⟨47756239224733347594697295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31837492816488898396464863 47756239224733347594697295)
      ·
        refine ⟨71634358837100021392045943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47756239224733347594697295 71634358837100021392045943)
        ·
          refine ⟨107451538255650032088068915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71634358837100021392045943 107451538255650032088068915)
          ·
            refine ⟨161177307383475048132103373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107451538255650032088068915 161177307383475048132103373)
            ·
              refine ⟨60441490268803143049538765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161177307383475048132103373 60441490268803143049538765)
              ·
                refine ⟨22665558850801178643577037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60441490268803143049538765 22665558850801178643577037)
                ·
                  refine ⟨8499584569050441991341389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22665558850801178643577037 8499584569050441991341389)
                  ·
                    refine ⟨3187344213393915746753021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8499584569050441991341389 3187344213393915746753021)
                    ·
                      refine ⟨1195254080022718405032383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3187344213393915746753021 1195254080022718405032383)
                      ·
                        rfl

theorem cell23_2327749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 3, 3].length) (baseStart_2327749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327749 prefixEnd_2327749 := by exact prefixLift 2327749
  have htrace : WordTrace (prefixWord ++ tailWord_2327749) baseStart_2327749 baseEnd_2327749 := by
    simpa [prefixWord, tailWord_2327749, baseEnd_2327749] using wordTrace_append hprefix tailTrace_2327749
  have hstable : (prefixWord ++ tailWord_2327749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327749).length < 2 ^ (prefixWord ++ tailWord_2327749).sum := by decide
  have hdescent : baseEnd_2327749 < baseStart_2327749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327829 : List Nat := [1, 3, 2, 1, 2, 1, 1, 5, 7]
def baseStart_2327829 : Nat := 118140960795 + 2327829 * 2 ^ 59
def prefixEnd_2327829 : Nat := 4983230072969 + 3 ^ 40 * 2327829 * 2
def baseEnd_2327829 : Nat := 132810573163897565781335

theorem tailTrace_2327829 : CollatzResearch.WordTrace tailWord_2327829 prefixEnd_2327829 132810573163897565781335 := by
  unfold tailWord_2327829
  simp only [CollatzResearch.WordTrace]
  refine ⟨84902898683680569386818541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56601932455787046257879027 84902898683680569386818541)
  ·
    refine ⟨31838587006380213520056953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84902898683680569386818541 31838587006380213520056953)
    ·
      refine ⟨23878940254785160140042715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31838587006380213520056953 23878940254785160140042715)
      ·
        refine ⟨35818410382177740210064073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23878940254785160140042715 35818410382177740210064073)
        ·
          refine ⟨26863807786633305157548055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35818410382177740210064073 26863807786633305157548055)
          ·
            refine ⟨40295711679949957736322083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26863807786633305157548055 40295711679949957736322083)
            ·
              refine ⟨60443567519924936604483125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40295711679949957736322083 60443567519924936604483125)
              ·
                refine ⟨5666584454992962806670293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60443567519924936604483125 5666584454992962806670293)
                ·
                  refine ⟨132810573163897565781335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5666584454992962806670293 132810573163897565781335)
                  ·
                    rfl

theorem cell23_2327829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 7].length) (baseStart_2327829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327829 prefixEnd_2327829 := by exact prefixLift 2327829
  have htrace : WordTrace (prefixWord ++ tailWord_2327829) baseStart_2327829 baseEnd_2327829 := by
    simpa [prefixWord, tailWord_2327829, baseEnd_2327829] using wordTrace_append hprefix tailTrace_2327829
  have hstable : (prefixWord ++ tailWord_2327829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327829).length < 2 ^ (prefixWord ++ tailWord_2327829).sum := by decide
  have hdescent : baseEnd_2327829 < baseStart_2327829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327840 : List Nat := [2, 1, 1, 5, 3, 1, 2, 1, 1, 4, 2]
def baseStart_2327840 : Nat := 118140960795 + 2327840 * 2 ^ 59
def prefixEnd_2327840 : Nat := 4983230072969 + 3 ^ 40 * 2327840 * 2
def baseEnd_2327840 : Nat := 1195300806762277548994465

theorem tailTrace_2327840 : CollatzResearch.WordTrace tailWord_2327840 prefixEnd_2327840 1195300806762277548994465 := by
  unfold tailWord_2327840
  simp only [CollatzResearch.WordTrace]
  refine ⟨42451649943320359132734487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56602199924427145510312649 42451649943320359132734487)
  ·
    refine ⟨63677474914980538699101731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42451649943320359132734487 63677474914980538699101731)
    ·
      refine ⟨95516212372470808048652597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63677474914980538699101731 95516212372470808048652597)
      ·
        refine ⟨8954644909919138254561181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95516212372470808048652597 8954644909919138254561181)
        ·
          refine ⟨3357991841219676845460443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8954644909919138254561181 3357991841219676845460443)
          ·
            refine ⟨5036987761829515268190665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3357991841219676845460443 5036987761829515268190665)
            ·
              refine ⟨3777740821372136451142999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5036987761829515268190665 3777740821372136451142999)
              ·
                refine ⟨5666611232058204676714499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3777740821372136451142999 5666611232058204676714499)
                ·
                  refine ⟨8499916848087307015071749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5666611232058204676714499 8499916848087307015071749)
                  ·
                    refine ⟨1593734409016370065325953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8499916848087307015071749 1593734409016370065325953)
                    ·
                      refine ⟨1195300806762277548994465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1593734409016370065325953 1195300806762277548994465)
                      ·
                        rfl

theorem cell23_2327840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_2327840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327840 prefixEnd_2327840 := by exact prefixLift 2327840
  have htrace : WordTrace (prefixWord ++ tailWord_2327840) baseStart_2327840 baseEnd_2327840 := by
    simpa [prefixWord, tailWord_2327840, baseEnd_2327840] using wordTrace_append hprefix tailTrace_2327840
  have hstable : (prefixWord ++ tailWord_2327840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327840).length < 2 ^ (prefixWord ++ tailWord_2327840).sum := by decide
  have hdescent : baseEnd_2327840 < baseStart_2327840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327873 : List Nat := [1, 2, 5, 2, 1, 1, 1, 2, 2, 3, 3]
def baseStart_2327873 : Nat := 118140960795 + 2327873 * 2 ^ 59
def prefixEnd_2327873 : Nat := 4983230072969 + 3 ^ 40 * 2327873 * 2
def baseEnd_2327873 : Nat := 1195317751623875919881813

theorem tailTrace_2327873 : CollatzResearch.WordTrace tailWord_2327873 prefixEnd_2327873 1195317751623875919881813 := by
  unfold tailWord_2327873
  simp only [CollatzResearch.WordTrace]
  refine ⟨84904503495521164901420273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56603002330347443267613515 84904503495521164901420273)
  ·
    refine ⟨63678377621640873676065205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84904503495521164901420273 63678377621640873676065205)
    ·
      refine ⟨5969847902028831907131113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63678377621640873676065205 5969847902028831907131113)
      ·
        refine ⟨4477385926521623930348335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5969847902028831907131113 4477385926521623930348335)
        ·
          refine ⟨6716078889782435895522503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4477385926521623930348335 6716078889782435895522503)
          ·
            refine ⟨10074118334673653843283755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6716078889782435895522503 10074118334673653843283755)
            ·
              refine ⟨15111177502010480764925633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10074118334673653843283755 15111177502010480764925633)
              ·
                refine ⟨11333383126507860573694225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15111177502010480764925633 11333383126507860573694225)
                ·
                  refine ⟨8500037344880895430270669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11333383126507860573694225 8500037344880895430270669)
                  ·
                    refine ⟨3187514004330335786351501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8500037344880895430270669 3187514004330335786351501)
                    ·
                      refine ⟨1195317751623875919881813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3187514004330335786351501 1195317751623875919881813)
                      ·
                        rfl

theorem cell23_2327873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_2327873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327873 prefixEnd_2327873 := by exact prefixLift 2327873
  have htrace : WordTrace (prefixWord ++ tailWord_2327873) baseStart_2327873 baseEnd_2327873 := by
    simpa [prefixWord, tailWord_2327873, baseEnd_2327873] using wordTrace_append hprefix tailTrace_2327873
  have hstable : (prefixWord ++ tailWord_2327873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327873).length < 2 ^ (prefixWord ++ tailWord_2327873).sum := by decide
  have hdescent : baseEnd_2327873 < baseStart_2327873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327906 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 2, 8]
def baseStart_2327906 : Nat := 118140960795 + 2327906 * 2 ^ 59
def prefixEnd_2327906 : Nat := 4983230072969 + 3 ^ 40 * 2327906 * 2
def baseEnd_2327906 : Nat := 398444898828491430256387

theorem tailTrace_2327906 : CollatzResearch.WordTrace tailWord_2327906 prefixEnd_2327906 398444898828491430256387 := by
  unfold tailWord_2327906
  simp only [CollatzResearch.WordTrace]
  refine ⟨21226426776100402884342893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56603804736267741024914381 21226426776100402884342893)
  ·
    refine ⟨7959910041037651081628585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21226426776100402884342893 7959910041037651081628585)
    ·
      refine ⟨5969932530778238311221439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7959910041037651081628585 5969932530778238311221439)
      ·
        refine ⟨8954898796167357466832159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5969932530778238311221439 8954898796167357466832159)
        ·
          refine ⟨13432348194251036200248239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8954898796167357466832159 13432348194251036200248239)
          ·
            refine ⟨20148522291376554300372359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13432348194251036200248239 20148522291376554300372359)
            ·
              refine ⟨30222783437064831450558539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20148522291376554300372359 30222783437064831450558539)
              ·
                refine ⟨45334175155597247175837809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30222783437064831450558539 45334175155597247175837809)
                ·
                  refine ⟨34000631366697935381878357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45334175155597247175837809 34000631366697935381878357)
                  ·
                    refine ⟨398444898828491430256387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34000631366697935381878357 398444898828491430256387)
                    ·
                      rfl

theorem cell23_2327906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_2327906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327906 prefixEnd_2327906 := by exact prefixLift 2327906
  have htrace : WordTrace (prefixWord ++ tailWord_2327906) baseStart_2327906 baseEnd_2327906 := by
    simpa [prefixWord, tailWord_2327906, baseEnd_2327906] using wordTrace_append hprefix tailTrace_2327906
  have hstable : (prefixWord ++ tailWord_2327906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327906).length < 2 ^ (prefixWord ++ tailWord_2327906).sum := by decide
  have hdescent : baseEnd_2327906 < baseStart_2327906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327919 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 10]
def baseStart_2327919 : Nat := 118140960795 + 2327919 * 2 ^ 59
def prefixEnd_2327919 : Nat := 4983230072969 + 3 ^ 40 * 2327919 * 2
def baseEnd_2327919 : Nat := 132815707970442526656289

theorem tailTrace_2327919 : CollatzResearch.WordTrace tailWord_2327919 prefixEnd_2327919 132815707970442526656289 := by
  unfold tailWord_2327919
  simp only [CollatzResearch.WordTrace]
  refine ⟨84906181253354514757594811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56604120835569676505063207 84906181253354514757594811)
  ·
    refine ⟨127359271880031772136392217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84906181253354514757594811 127359271880031772136392217)
    ·
      refine ⟨95519453910023829102294163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127359271880031772136392217 95519453910023829102294163)
      ·
        refine ⟨143279180865035743653441245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95519453910023829102294163 143279180865035743653441245)
        ·
          refine ⟨53729692824388403870040467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143279180865035743653441245 53729692824388403870040467)
          ·
            refine ⟨80594539236582605805060701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53729692824388403870040467 80594539236582605805060701)
            ·
              refine ⟨30222952213718477176897763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80594539236582605805060701 30222952213718477176897763)
              ·
                refine ⟨45334428320577715765346645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30222952213718477176897763 45334428320577715765346645)
                ·
                  refine ⟨132815707970442526656289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 45334428320577715765346645 132815707970442526656289)
                  ·
                    rfl

theorem cell23_2327919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 10].length) (baseStart_2327919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327919 prefixEnd_2327919 := by exact prefixLift 2327919
  have htrace : WordTrace (prefixWord ++ tailWord_2327919) baseStart_2327919 baseEnd_2327919 := by
    simpa [prefixWord, tailWord_2327919, baseEnd_2327919] using wordTrace_append hprefix tailTrace_2327919
  have hstable : (prefixWord ++ tailWord_2327919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327919).length < 2 ^ (prefixWord ++ tailWord_2327919).sum := by decide
  have hdescent : baseEnd_2327919 < baseStart_2327919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327933 : List Nat := [1, 4, 1, 1, 2, 2, 3, 2, 2, 2, 3]
def baseStart_2327933 : Nat := 118140960795 + 2327933 * 2 ^ 59
def prefixEnd_2327933 : Nat := 4983230072969 + 3 ^ 40 * 2327933 * 2
def baseEnd_2327933 : Nat := 1195348560463145685131537

theorem tailTrace_2327933 : CollatzResearch.WordTrace tailWord_2327933 prefixEnd_2327933 1195348560463145685131537 := by
  unfold tailWord_2327933
  simp only [CollatzResearch.WordTrace]
  refine ⟨84906691875303795148604453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56604461250202530099069635 84906691875303795148604453)
  ·
    refine ⟨15920004726619461590363335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84906691875303795148604453 15920004726619461590363335)
    ·
      refine ⟨23880007089929192385545003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15920004726619461590363335 23880007089929192385545003)
      ·
        refine ⟨35820010634893788578317505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23880007089929192385545003 35820010634893788578317505)
        ·
          refine ⟨26865007976170341433738129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35820010634893788578317505 26865007976170341433738129)
          ·
            refine ⟨20148755982127756075303597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26865007976170341433738129 20148755982127756075303597)
            ·
              refine ⟨7555783493297908528238849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20148755982127756075303597 7555783493297908528238849)
              ·
                refine ⟨5666837619973431396179137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7555783493297908528238849 5666837619973431396179137)
                ·
                  refine ⟨4250128214980073547134353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5666837619973431396179137 4250128214980073547134353)
                  ·
                    refine ⟨3187596161235055160350765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4250128214980073547134353 3187596161235055160350765)
                    ·
                      refine ⟨1195348560463145685131537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3187596161235055160350765 1195348560463145685131537)
                      ·
                        rfl

theorem cell23_2327933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_2327933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327933 prefixEnd_2327933 := by exact prefixLift 2327933
  have htrace : WordTrace (prefixWord ++ tailWord_2327933) baseStart_2327933 baseEnd_2327933 := by
    simpa [prefixWord, tailWord_2327933, baseEnd_2327933] using wordTrace_append hprefix tailTrace_2327933
  have hstable : (prefixWord ++ tailWord_2327933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327933).length < 2 ^ (prefixWord ++ tailWord_2327933).sum := by decide
  have hdescent : baseEnd_2327933 < baseStart_2327933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327940 : List Nat := [2, 3, 2, 1, 1, 5, 1, 1, 3, 4]
def baseStart_2327940 : Nat := 118140960795 + 2327940 * 2 ^ 59
def prefixEnd_2327940 : Nat := 4983230072969 + 3 ^ 40 * 2327940 * 2
def baseEnd_2327940 : Nat := 398450718275909052581335

theorem tailTrace_2327940 : CollatzResearch.WordTrace tailWord_2327940 prefixEnd_2327940 398450718275909052581335 := by
  unfold tailWord_2327940
  simp only [CollatzResearch.WordTrace]
  refine ⟨42453473593139217672054637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56604631457518956896072849 42453473593139217672054637)
  ·
    refine ⟨15920052597427206627020489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42453473593139217672054637 15920052597427206627020489)
    ·
      refine ⟨11940039448070404970265367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15920052597427206627020489 11940039448070404970265367)
      ·
        refine ⟨17910059172105607455398051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11940039448070404970265367 17910059172105607455398051)
        ·
          refine ⟨26865088758158411183097077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17910059172105607455398051 26865088758158411183097077)
          ·
            refine ⟨2518602071077351048415351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26865088758158411183097077 2518602071077351048415351)
            ·
              refine ⟨3777903106616026572623027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2518602071077351048415351 3777903106616026572623027)
              ·
                refine ⟨5666854659924039858934541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3777903106616026572623027 5666854659924039858934541)
                ·
                  refine ⟨2125070497471514947100453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5666854659924039858934541 2125070497471514947100453)
                  ·
                    refine ⟨398450718275909052581335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2125070497471514947100453 398450718275909052581335)
                    ·
                      rfl

theorem cell23_2327940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_2327940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327940 prefixEnd_2327940 := by exact prefixLift 2327940
  have htrace : WordTrace (prefixWord ++ tailWord_2327940) baseStart_2327940 baseEnd_2327940 := by
    simpa [prefixWord, tailWord_2327940, baseEnd_2327940] using wordTrace_append hprefix tailTrace_2327940
  have hstable : (prefixWord ++ tailWord_2327940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327940).length < 2 ^ (prefixWord ++ tailWord_2327940).sum := by decide
  have hdescent : baseEnd_2327940 < baseStart_2327940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2327997 : List Nat := [1, 4, 1, 2, 2, 1, 3, 4, 1, 1, 3]
def baseStart_2327997 : Nat := 118140960795 + 2327997 * 2 ^ 59
def prefixEnd_2327997 : Nat := 4983230072969 + 3 ^ 40 * 2327997 * 2
def baseEnd_2327997 : Nat := 1195381423225033434731243

theorem tailTrace_2327997 : CollatzResearch.WordTrace tailWord_2327997 prefixEnd_2327997 1195381423225033434731243 := by
  unfold tailWord_2327997
  simp only [CollatzResearch.WordTrace]
  refine ⟨84909026147071934078934245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56606017431381289385956163 84909026147071934078934245)
  ·
    refine ⟨15920442402575987639800171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84909026147071934078934245 15920442402575987639800171)
    ·
      refine ⟨23880663603863981459700257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15920442402575987639800171 23880663603863981459700257)
      ·
        refine ⟨17910497702897986094775193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23880663603863981459700257 17910497702897986094775193)
        ·
          refine ⟨13432873277173489571081395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17910497702897986094775193 13432873277173489571081395)
          ·
            refine ⟨20149309915760234356622093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13432873277173489571081395 20149309915760234356622093)
            ·
              refine ⟨7555991218410087883733285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20149309915760234356622093 7555991218410087883733285)
              ·
                refine ⟨1416748353451891478199991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7555991218410087883733285 1416748353451891478199991)
                ·
                  refine ⟨2125122530177837217299987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1416748353451891478199991 2125122530177837217299987)
                  ·
                    refine ⟨3187683795266755825949981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2125122530177837217299987 3187683795266755825949981)
                    ·
                      refine ⟨1195381423225033434731243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3187683795266755825949981 1195381423225033434731243)
                      ·
                        rfl

theorem cell23_2327997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_2327997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2327997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2327997 prefixEnd_2327997 := by exact prefixLift 2327997
  have htrace : WordTrace (prefixWord ++ tailWord_2327997) baseStart_2327997 baseEnd_2327997 := by
    simpa [prefixWord, tailWord_2327997, baseEnd_2327997] using wordTrace_append hprefix tailTrace_2327997
  have hstable : (prefixWord ++ tailWord_2327997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2327997).length < 2 ^ (prefixWord ++ tailWord_2327997).sum := by decide
  have hdescent : baseEnd_2327997 < baseStart_2327997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2327997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328016 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 4]
def baseStart_2328016 : Nat := 118140960795 + 2328016 * 2 ^ 59
def prefixEnd_2328016 : Nat := 4983230072969 + 3 ^ 40 * 2328016 * 2
def baseEnd_2328016 : Nat := 1195391179357468860393655

theorem tailTrace_2328016 : CollatzResearch.WordTrace tailWord_2328016 prefixEnd_2328016 1195391179357468860393655 := by
  unfold tailWord_2328016
  simp only [CollatzResearch.WordTrace]
  refine ⟨42454859567001550161937951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56606479422668733549250601 42454859567001550161937951)
  ·
    refine ⟨63682289350502325242906927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42454859567001550161937951 63682289350502325242906927)
    ·
      refine ⟨95523434025753487864360391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63682289350502325242906927 95523434025753487864360391)
      ·
        refine ⟨143285151038630231796540587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95523434025753487864360391 143285151038630231796540587)
        ·
          refine ⟨214927726557945347694810881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143285151038630231796540587 214927726557945347694810881)
          ·
            refine ⟨161195794918459010771108161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214927726557945347694810881 161195794918459010771108161)
            ·
              refine ⟨120896846188844258078331121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161195794918459010771108161 120896846188844258078331121)
              ·
                refine ⟨90672634641633193558748341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120896846188844258078331121 90672634641633193558748341)
                ·
                  refine ⟨8500559497653111896132657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90672634641633193558748341 8500559497653111896132657)
                  ·
                    refine ⟨6375419623239833922099493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8500559497653111896132657 6375419623239833922099493)
                    ·
                      refine ⟨1195391179357468860393655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6375419623239833922099493 1195391179357468860393655)
                      ·
                        rfl

theorem cell23_2328016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 4].length) (baseStart_2328016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328016 prefixEnd_2328016 := by exact prefixLift 2328016
  have htrace : WordTrace (prefixWord ++ tailWord_2328016) baseStart_2328016 baseEnd_2328016 := by
    simpa [prefixWord, tailWord_2328016, baseEnd_2328016] using wordTrace_append hprefix tailTrace_2328016
  have hstable : (prefixWord ++ tailWord_2328016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328016).length < 2 ^ (prefixWord ++ tailWord_2328016).sum := by decide
  have hdescent : baseEnd_2328016 < baseStart_2328016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328033 : List Nat := [1, 2, 3, 1, 2, 3, 2, 2, 1, 2, 4]
def baseStart_2328033 : Nat := 118140960795 + 2328033 * 2 ^ 59
def prefixEnd_2328033 : Nat := 4983230072969 + 3 ^ 40 * 2328033 * 2
def baseEnd_2328033 : Nat := 1195399908528595293881077

theorem tailTrace_2328033 : CollatzResearch.WordTrace tailWord_2328033 prefixEnd_2328033 1195399908528595293881077 := by
  unfold tailWord_2328033
  simp only [CollatzResearch.WordTrace]
  refine ⟨84910339174941512227244753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56606892783294341484829835 84910339174941512227244753)
  ·
    refine ⟨63682754381206134170433565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84910339174941512227244753 63682754381206134170433565)
    ·
      refine ⟨23881032892952300313912587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63682754381206134170433565 23881032892952300313912587)
      ·
        refine ⟨35821549339428450470868881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23881032892952300313912587 35821549339428450470868881)
        ·
          refine ⟨26866162004571337853151661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35821549339428450470868881 26866162004571337853151661)
          ·
            refine ⟨10074810751714251694931873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26866162004571337853151661 10074810751714251694931873)
            ·
              refine ⟨7556108063785688771198905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10074810751714251694931873 7556108063785688771198905)
              ·
                refine ⟨5667081047839266578399179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7556108063785688771198905 5667081047839266578399179)
                ·
                  refine ⟨8500621571758899867598769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5667081047839266578399179 8500621571758899867598769)
                  ·
                    refine ⟨6375466178819174900699077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8500621571758899867598769 6375466178819174900699077)
                    ·
                      refine ⟨1195399908528595293881077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6375466178819174900699077 1195399908528595293881077)
                      ·
                        rfl

theorem cell23_2328033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_2328033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328033 prefixEnd_2328033 := by exact prefixLift 2328033
  have htrace : WordTrace (prefixWord ++ tailWord_2328033) baseStart_2328033 baseEnd_2328033 := by
    simpa [prefixWord, tailWord_2328033, baseEnd_2328033] using wordTrace_append hprefix tailTrace_2328033
  have hstable : (prefixWord ++ tailWord_2328033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328033).length < 2 ^ (prefixWord ++ tailWord_2328033).sum := by decide
  have hdescent : baseEnd_2328033 < baseStart_2328033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328037 : List Nat := [1, 3, 1, 5, 1, 1, 4, 1, 1, 1, 4]
def baseStart_2328037 : Nat := 118140960795 + 2328037 * 2 ^ 59
def prefixEnd_2328037 : Nat := 4983230072969 + 3 ^ 40 * 2328037 * 2
def baseEnd_2328037 : Nat := 1195401962451213278231059

theorem tailTrace_2328037 : CollatzResearch.WordTrace tailWord_2328037 prefixEnd_2328037 1195401962451213278231059 := by
  unfold tailWord_2328037
  simp only [CollatzResearch.WordTrace]
  refine ⟨84910485066927020910390365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56606990044618013940260243 84910485066927020910390365)
  ·
    refine ⟨31841431900097632841396387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84910485066927020910390365 31841431900097632841396387)
    ·
      refine ⟨47762147850146449262094581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31841431900097632841396387 47762147850146449262094581)
      ·
        refine ⟨4477701360951229618321367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47762147850146449262094581 4477701360951229618321367)
        ·
          refine ⟨6716552041426844427482051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4477701360951229618321367 6716552041426844427482051)
          ·
            refine ⟨10074828062140266641223077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6716552041426844427482051 10074828062140266641223077)
            ·
              refine ⟨1889030261651299995229327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10074828062140266641223077 1889030261651299995229327)
              ·
                refine ⟨2833545392476949992843991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1889030261651299995229327 2833545392476949992843991)
                ·
                  refine ⟨4250318088715424989265987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2833545392476949992843991 4250318088715424989265987)
                  ·
                    refine ⟨6375477133073137483898981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4250318088715424989265987 6375477133073137483898981)
                    ·
                      refine ⟨1195401962451213278231059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6375477133073137483898981 1195401962451213278231059)
                      ·
                        rfl

theorem cell23_2328037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_2328037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328037 prefixEnd_2328037 := by exact prefixLift 2328037
  have htrace : WordTrace (prefixWord ++ tailWord_2328037) baseStart_2328037 baseEnd_2328037 := by
    simpa [prefixWord, tailWord_2328037, baseEnd_2328037] using wordTrace_append hprefix tailTrace_2328037
  have hstable : (prefixWord ++ tailWord_2328037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328037).length < 2 ^ (prefixWord ++ tailWord_2328037).sum := by decide
  have hdescent : baseEnd_2328037 < baseStart_2328037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328040 : List Nat := [2, 1, 4, 1, 1, 2, 3, 3, 1, 2, 3]
def baseStart_2328040 : Nat := 118140960795 + 2328040 * 2 ^ 59
def prefixEnd_2328040 : Nat := 4983230072969 + 3 ^ 40 * 2328040 * 2
def baseEnd_2328040 : Nat := 1195403502893176766493545

theorem tailTrace_2328040 : CollatzResearch.WordTrace tailWord_2328040 prefixEnd_2328040 1195403502893176766493545 := by
  unfold tailWord_2328040
  simp only [CollatzResearch.WordTrace]
  refine ⟨42455297242958076211374787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56607062990610768281833049 42455297242958076211374787)
  ·
    refine ⟨63682945864437114317062181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42455297242958076211374787 63682945864437114317062181)
    ·
      refine ⟨11940552349581958934449159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63682945864437114317062181 11940552349581958934449159)
      ·
        refine ⟨17910828524372938401673739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11940552349581958934449159 17910828524372938401673739)
        ·
          refine ⟨26866242786559407602510609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17910828524372938401673739 26866242786559407602510609)
          ·
            refine ⟨20149682089919555701882957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26866242786559407602510609 20149682089919555701882957)
            ·
              refine ⟨7556130783719833388206109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20149682089919555701882957 7556130783719833388206109)
              ·
                refine ⟨2833549043894937520577291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7556130783719833388206109 2833549043894937520577291)
                ·
                  refine ⟨4250323565842406280865937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2833549043894937520577291 4250323565842406280865937)
                  ·
                    refine ⟨3187742674381804710649453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4250323565842406280865937 3187742674381804710649453)
                    ·
                      refine ⟨1195403502893176766493545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3187742674381804710649453 1195403502893176766493545)
                      ·
                        rfl

theorem cell23_2328040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_2328040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328040 prefixEnd_2328040 := by exact prefixLift 2328040
  have htrace : WordTrace (prefixWord ++ tailWord_2328040) baseStart_2328040 baseEnd_2328040 := by
    simpa [prefixWord, tailWord_2328040, baseEnd_2328040] using wordTrace_append hprefix tailTrace_2328040
  have hstable : (prefixWord ++ tailWord_2328040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328040).length < 2 ^ (prefixWord ++ tailWord_2328040).sum := by decide
  have hdescent : baseEnd_2328040 < baseStart_2328040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328054 : List Nat := [5, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2]
def baseStart_2328054 : Nat := 118140960795 + 2328054 * 2 ^ 59
def prefixEnd_2328054 : Nat := 4983230072969 + 3 ^ 40 * 2328054 * 2
def baseEnd_2328054 : Nat := 1195410691622339711718481

theorem tailTrace_2328054 : CollatzResearch.WordTrace tailWord_2328054 prefixEnd_2328054 1195410691622339711718481 := by
  unfold tailWord_2328054
  simp only [CollatzResearch.WordTrace]
  refine ⟨5306944069241589550859951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56607403405243621875839477 5306944069241589550859951)
  ·
    refine ⟨7960416103862384326289927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5306944069241589550859951 7960416103862384326289927)
    ·
      refine ⟨11940624155793576489434891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7960416103862384326289927 11940624155793576489434891)
      ·
        refine ⟨17910936233690364734152337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11940624155793576489434891 17910936233690364734152337)
        ·
          refine ⟨13433202175267773550614253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17910936233690364734152337 13433202175267773550614253)
          ·
            refine ⟨5037450815725415081480345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13433202175267773550614253 5037450815725415081480345)
            ·
              refine ⟨3778088111794061311110259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5037450815725415081480345 3778088111794061311110259)
              ·
                refine ⟨5667132167691091966665389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3778088111794061311110259 5667132167691091966665389)
                ·
                  refine ⟨2125174562884159487499521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5667132167691091966665389 2125174562884159487499521)
                  ·
                    refine ⟨1593880922163119615624641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2125174562884159487499521 1593880922163119615624641)
                    ·
                      refine ⟨1195410691622339711718481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1593880922163119615624641 1195410691622339711718481)
                      ·
                        rfl

theorem cell23_2328054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_2328054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328054 prefixEnd_2328054 := by exact prefixLift 2328054
  have htrace : WordTrace (prefixWord ++ tailWord_2328054) baseStart_2328054 baseEnd_2328054 := by
    simpa [prefixWord, tailWord_2328054, baseEnd_2328054] using wordTrace_append hprefix tailTrace_2328054
  have hstable : (prefixWord ++ tailWord_2328054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328054).length < 2 ^ (prefixWord ++ tailWord_2328054).sum := by decide
  have hdescent : baseEnd_2328054 < baseStart_2328054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328063 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 2, 7, 2]
def baseStart_2328063 : Nat := 118140960795 + 2328063 * 2 ^ 59
def prefixEnd_2328063 : Nat := 4983230072969 + 3 ^ 40 * 2328063 * 2
def baseEnd_2328063 : Nat := 1195415312948230176505939

theorem tailTrace_2328063 : CollatzResearch.WordTrace tailWord_2328063 prefixEnd_2328063 1195415312948230176505939 := by
  unfold tailWord_2328063
  simp only [CollatzResearch.WordTrace]
  refine ⟨84911433364832827350836843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56607622243221884900557895 84911433364832827350836843)
  ·
    refine ⟨127367150047249241026255265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84911433364832827350836843 127367150047249241026255265)
    ·
      refine ⟨95525362535436930769691449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127367150047249241026255265 95525362535436930769691449)
      ·
        refine ⟨71644021901577698077268587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95525362535436930769691449 71644021901577698077268587)
        ·
          refine ⟨107466032852366547115902881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71644021901577698077268587 107466032852366547115902881)
          ·
            refine ⟨80599524639274910336927161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107466032852366547115902881 80599524639274910336927161)
            ·
              refine ⟨60449643479456182752695371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80599524639274910336927161 60449643479456182752695371)
              ·
                refine ⟨90674465219184274129043057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60449643479456182752695371 90674465219184274129043057)
                ·
                  refine ⟨68005848914388205596782293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90674465219184274129043057 68005848914388205596782293)
                  ·
                    refine ⟨1593887083930973568674585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 68005848914388205596782293 1593887083930973568674585)
                    ·
                      refine ⟨1195415312948230176505939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1593887083930973568674585 1195415312948230176505939)
                      ·
                        rfl

theorem cell23_2328063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 7, 2].length) (baseStart_2328063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328063 prefixEnd_2328063 := by exact prefixLift 2328063
  have htrace : WordTrace (prefixWord ++ tailWord_2328063) baseStart_2328063 baseEnd_2328063 := by
    simpa [prefixWord, tailWord_2328063, baseEnd_2328063] using wordTrace_append hprefix tailTrace_2328063
  have hstable : (prefixWord ++ tailWord_2328063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328063).length < 2 ^ (prefixWord ++ tailWord_2328063).sum := by decide
  have hdescent : baseEnd_2328063 < baseStart_2328063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328077 : List Nat := [1, 7, 1, 1, 2, 1, 1, 9]
def baseStart_2328077 : Nat := 118140960795 + 2328077 * 2 ^ 59
def prefixEnd_2328077 : Nat := 4983230072969 + 3 ^ 40 * 2328077 * 2
def baseEnd_2328077 : Nat := 44274907469533078582625

theorem tailTrace_2328077 : CollatzResearch.WordTrace tailWord_2328077 prefixEnd_2328077 44274907469533078582625 := by
  unfold tailWord_2328077
  simp only [CollatzResearch.WordTrace]
  refine ⟨84911943986782107741846485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56607962657854738494564323 84911943986782107741846485)
  ·
    refine ⟨1990123687190205650199527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 84911943986782107741846485 1990123687190205650199527)
    ·
      refine ⟨2985185530785308475299291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1990123687190205650199527 2985185530785308475299291)
      ·
        refine ⟨4477778296177962712948937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2985185530785308475299291 4477778296177962712948937)
        ·
          refine ⟨3358333722133472034711703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4477778296177962712948937 3358333722133472034711703)
          ·
            refine ⟨5037500583200208052067555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3358333722133472034711703 5037500583200208052067555)
            ·
              refine ⟨7556250874800312078101333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5037500583200208052067555 7556250874800312078101333)
              ·
                refine ⟨44274907469533078582625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7556250874800312078101333 44274907469533078582625)
                ·
                  rfl

theorem cell23_2328077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 9].length) (baseStart_2328077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328077 prefixEnd_2328077 := by exact prefixLift 2328077
  have htrace : WordTrace (prefixWord ++ tailWord_2328077) baseStart_2328077 baseEnd_2328077 := by
    simpa [prefixWord, tailWord_2328077, baseEnd_2328077] using wordTrace_append hprefix tailTrace_2328077
  have hstable : (prefixWord ++ tailWord_2328077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328077).length < 2 ^ (prefixWord ++ tailWord_2328077).sum := by decide
  have hdescent : baseEnd_2328077 < baseStart_2328077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328088 : List Nat := [2, 1, 2, 3, 5, 1, 1, 3, 1, 2, 2]
def baseStart_2328088 : Nat := 118140960795 + 2328088 * 2 ^ 59
def prefixEnd_2328088 : Nat := 4983230072969 + 3 ^ 40 * 2328088 * 2
def baseEnd_2328088 : Nat := 1195428149964592578693325

theorem tailTrace_2328088 : CollatzResearch.WordTrace tailWord_2328088 prefixEnd_2328088 1195428149964592578693325 := by
  unfold tailWord_2328088
  simp only [CollatzResearch.WordTrace]
  refine ⟨42456172594871128310248459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56608230126494837746997945 42456172594871128310248459)
  ·
    refine ⟨63684258892306692465372689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42456172594871128310248459 63684258892306692465372689)
    ·
      refine ⟨47763194169230019349029517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63684258892306692465372689 47763194169230019349029517)
      ·
        refine ⟨17911197813461257255886069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47763194169230019349029517 17911197813461257255886069)
        ·
          refine ⟨1679174795011992867739319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17911197813461257255886069 1679174795011992867739319)
          ·
            refine ⟨2518762192517989301608979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1679174795011992867739319 2518762192517989301608979)
            ·
              refine ⟨3778143288776983952413469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2518762192517989301608979 3778143288776983952413469)
              ·
                refine ⟨1416803733291368982155051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3778143288776983952413469 1416803733291368982155051)
                ·
                  refine ⟨2125205599937053473232577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1416803733291368982155051 2125205599937053473232577)
                  ·
                    refine ⟨1593904199952790104924433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2125205599937053473232577 1593904199952790104924433)
                    ·
                      refine ⟨1195428149964592578693325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1593904199952790104924433 1195428149964592578693325)
                      ·
                        rfl

theorem cell23_2328088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_2328088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328088 prefixEnd_2328088 := by exact prefixLift 2328088
  have htrace : WordTrace (prefixWord ++ tailWord_2328088) baseStart_2328088 baseEnd_2328088 := by
    simpa [prefixWord, tailWord_2328088, baseEnd_2328088] using wordTrace_append hprefix tailTrace_2328088
  have hstable : (prefixWord ++ tailWord_2328088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328088).length < 2 ^ (prefixWord ++ tailWord_2328088).sum := by decide
  have hdescent : baseEnd_2328088 < baseStart_2328088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328094 : List Nat := [4, 3, 3, 1, 1, 2, 9]
def baseStart_2328094 : Nat := 118140960795 + 2328094 * 2 ^ 59
def prefixEnd_2328094 : Nat := 4983230072969 + 3 ^ 40 * 2328094 * 2
def baseEnd_2328094 : Nat := 14758410257389130311337

theorem tailTrace_2328094 : CollatzResearch.WordTrace tailWord_2328094 prefixEnd_2328094 14758410257389130311337 := by
  unfold tailWord_2328094
  simp only [CollatzResearch.WordTrace]
  refine ⟨10614070503465064955651917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56608376018480346430143557 10614070503465064955651917)
  ·
    refine ⟨3980276438799399358369469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10614070503465064955651917 3980276438799399358369469)
    ·
      refine ⟨1492603664549774759388551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3980276438799399358369469 1492603664549774759388551)
      ·
        refine ⟨2238905496824662139082827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1492603664549774759388551 2238905496824662139082827)
        ·
          refine ⟨3358358245236993208624241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2238905496824662139082827 3358358245236993208624241)
          ·
            refine ⟨2518768683927744906468181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3358358245236993208624241 2518768683927744906468181)
            ·
              refine ⟨14758410257389130311337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2518768683927744906468181 14758410257389130311337)
              ·
                rfl

theorem cell23_2328094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 9].length) (baseStart_2328094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328094 prefixEnd_2328094 := by exact prefixLift 2328094
  have htrace : WordTrace (prefixWord ++ tailWord_2328094) baseStart_2328094 baseEnd_2328094 := by
    simpa [prefixWord, tailWord_2328094, baseEnd_2328094] using wordTrace_append hprefix tailTrace_2328094
  have hstable : (prefixWord ++ tailWord_2328094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328094).length < 2 ^ (prefixWord ++ tailWord_2328094).sum := by decide
  have hdescent : baseEnd_2328094 < baseStart_2328094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328097 : List Nat := [1, 2, 3, 2, 2, 2, 2, 3, 1, 3, 2]
def baseStart_2328097 : Nat := 118140960795 + 2328097 * 2 ^ 59
def prefixEnd_2328097 : Nat := 4983230072969 + 3 ^ 40 * 2328097 * 2
def baseEnd_2328097 : Nat := 1195432771290483043480783

theorem tailTrace_2328097 : CollatzResearch.WordTrace tailWord_2328097 prefixEnd_2328097 1195432771290483043480783 := by
  unfold tailWord_2328097
  simp only [CollatzResearch.WordTrace]
  refine ⟨84912673446709651157574545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56608448964473100771716363 84912673446709651157574545)
  ·
    refine ⟨63684505085032238368180909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84912673446709651157574545 63684505085032238368180909)
    ·
      refine ⟨23881689406887089388067841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63684505085032238368180909 23881689406887089388067841)
      ·
        refine ⟨17911267055165317041050881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23881689406887089388067841 17911267055165317041050881)
        ·
          refine ⟨13433450291373987780788161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17911267055165317041050881 13433450291373987780788161)
          ·
            refine ⟨10075087718530490835591121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13433450291373987780788161 10075087718530490835591121)
            ·
              refine ⟨7556315788897868126693341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10075087718530490835591121 7556315788897868126693341)
              ·
                refine ⟨2833618420836700547510003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7556315788897868126693341 2833618420836700547510003)
                ·
                  refine ⟨4250427631255050821265005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2833618420836700547510003 4250427631255050821265005)
                  ·
                    refine ⟨1593910361720644057974377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4250427631255050821265005 1593910361720644057974377)
                    ·
                      refine ⟨1195432771290483043480783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1593910361720644057974377 1195432771290483043480783)
                      ·
                        rfl

theorem cell23_2328097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_2328097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328097 prefixEnd_2328097 := by exact prefixLift 2328097
  have htrace : WordTrace (prefixWord ++ tailWord_2328097) baseStart_2328097 baseEnd_2328097 := by
    simpa [prefixWord, tailWord_2328097, baseEnd_2328097] using wordTrace_append hprefix tailTrace_2328097
  have hstable : (prefixWord ++ tailWord_2328097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328097).length < 2 ^ (prefixWord ++ tailWord_2328097).sum := by decide
  have hdescent : baseEnd_2328097 < baseStart_2328097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328113 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 2, 4, 3]
def baseStart_2328113 : Nat := 118140960795 + 2328113 * 2 ^ 59
def prefixEnd_2328113 : Nat := 4983230072969 + 3 ^ 40 * 2328113 * 2
def baseEnd_2328113 : Nat := 1195440986980954980880709

theorem tailTrace_2328113 : CollatzResearch.WordTrace tailWord_2328113 prefixEnd_2328113 1195440986980954980880709 := by
  unfold tailWord_2328113
  simp only [CollatzResearch.WordTrace]
  refine ⟨84913257014651685890156993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56608838009767790593437995 84913257014651685890156993)
  ·
    refine ⟨63684942760988764417617745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84913257014651685890156993 63684942760988764417617745)
    ·
      refine ⟨47763707070741573313213309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63684942760988764417617745 47763707070741573313213309)
      ·
        refine ⟨17911390151528089992454991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47763707070741573313213309 17911390151528089992454991)
        ·
          refine ⟨26867085227292134988682487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17911390151528089992454991 26867085227292134988682487)
          ·
            refine ⟨40300627840938202483023731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26867085227292134988682487 40300627840938202483023731)
            ·
              refine ⟨60450941761407303724535597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40300627840938202483023731 60450941761407303724535597)
              ·
                refine ⟨22669103160527738896700849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60450941761407303724535597 22669103160527738896700849)
                ·
                  refine ⟨17001827370395804172525637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22669103160527738896700849 17001827370395804172525637)
                  ·
                    refine ⟨3187842631949213282348557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17001827370395804172525637 3187842631949213282348557)
                    ·
                      refine ⟨1195440986980954980880709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3187842631949213282348557 1195440986980954980880709)
                      ·
                        rfl

theorem cell23_2328113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_2328113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328113 prefixEnd_2328113 := by exact prefixLift 2328113
  have htrace : WordTrace (prefixWord ++ tailWord_2328113) baseStart_2328113 baseEnd_2328113 := by
    simpa [prefixWord, tailWord_2328113, baseEnd_2328113] using wordTrace_append hprefix tailTrace_2328113
  have hstable : (prefixWord ++ tailWord_2328113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328113).length < 2 ^ (prefixWord ++ tailWord_2328113).sum := by decide
  have hdescent : baseEnd_2328113 < baseStart_2328113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328143 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 4, 3, 3]
def baseStart_2328143 : Nat := 118140960795 + 2328143 * 2 ^ 59
def prefixEnd_2328143 : Nat := 4983230072969 + 3 ^ 40 * 2328143 * 2
def baseEnd_2328143 : Nat := 1195456391400589863505571

theorem tailTrace_2328143 : CollatzResearch.WordTrace tailWord_2328143 prefixEnd_2328143 1195456391400589863505571 := by
  unfold tailWord_2328143
  simp only [CollatzResearch.WordTrace]
  refine ⟨84914351204543001013749083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56609567469695334009166055 84914351204543001013749083)
  ·
    refine ⟨127371526806814501520623625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84914351204543001013749083 127371526806814501520623625)
    ·
      refine ⟨95528645105110876140467719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127371526806814501520623625 95528645105110876140467719)
      ·
        refine ⟨143292967657666314210701579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95528645105110876140467719 143292967657666314210701579)
        ·
          refine ⟨214939451486499471316052369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143292967657666314210701579 214939451486499471316052369)
          ·
            refine ⟨161204588614874603487039277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214939451486499471316052369 161204588614874603487039277)
            ·
              refine ⟨60451720730577976307639729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161204588614874603487039277 60451720730577976307639729)
              ·
                refine ⟨45338790547933482230729797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60451720730577976307639729 45338790547933482230729797)
                ·
                  refine ⟨8501023227737527918261837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45338790547933482230729797 8501023227737527918261837)
                  ·
                    refine ⟨3187883710401572969348189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8501023227737527918261837 3187883710401572969348189)
                    ·
                      refine ⟨1195456391400589863505571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3187883710401572969348189 1195456391400589863505571)
                      ·
                        rfl

theorem cell23_2328143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 3, 3].length) (baseStart_2328143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328143 prefixEnd_2328143 := by exact prefixLift 2328143
  have htrace : WordTrace (prefixWord ++ tailWord_2328143) baseStart_2328143 baseEnd_2328143 := by
    simpa [prefixWord, tailWord_2328143, baseEnd_2328143] using wordTrace_append hprefix tailTrace_2328143
  have hstable : (prefixWord ++ tailWord_2328143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328143).length < 2 ^ (prefixWord ++ tailWord_2328143).sum := by decide
  have hdescent : baseEnd_2328143 < baseStart_2328143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328167 : List Nat := [1, 1, 5, 1, 1, 1, 6, 2, 5]
def baseStart_2328167 : Nat := 118140960795 + 2328167 * 2 ^ 59
def prefixEnd_2328167 : Nat := 4983230072969 + 3 ^ 40 * 2328167 * 2
def baseEnd_2328167 : Nat := 132829857215144196622829

theorem tailTrace_2328167 : CollatzResearch.WordTrace tailWord_2328167 prefixEnd_2328167 132829857215144196622829 := by
  unfold tailWord_2328167
  simp only [CollatzResearch.WordTrace]
  refine ⟨84915226556456053112622755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56610151037637368741748503 84915226556456053112622755)
  ·
    refine ⟨127372839834684079668934133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84915226556456053112622755 127372839834684079668934133)
    ·
      refine ⟨11941203734501632468962575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 127372839834684079668934133 11941203734501632468962575)
      ·
        refine ⟨17911805601752448703443863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11941203734501632468962575 17911805601752448703443863)
        ·
          refine ⟨26867708402628673055165795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17911805601752448703443863 26867708402628673055165795)
          ·
            refine ⟨40301562603943009582748693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26867708402628673055165795 40301562603943009582748693)
            ·
              refine ⟨1889135747059828574191345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40301562603943009582748693 1889135747059828574191345)
              ·
                refine ⟨1416851810294871430643509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1889135747059828574191345 1416851810294871430643509)
                ·
                  refine ⟨132829857215144196622829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1416851810294871430643509 132829857215144196622829)
                  ·
                    rfl

theorem cell23_2328167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 2, 5].length) (baseStart_2328167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328167 prefixEnd_2328167 := by exact prefixLift 2328167
  have htrace : WordTrace (prefixWord ++ tailWord_2328167) baseStart_2328167 baseEnd_2328167 := by
    simpa [prefixWord, tailWord_2328167, baseEnd_2328167] using wordTrace_append hprefix tailTrace_2328167
  have hstable : (prefixWord ++ tailWord_2328167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328167).length < 2 ^ (prefixWord ++ tailWord_2328167).sum := by decide
  have hdescent : baseEnd_2328167 < baseStart_2328167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328183 : List Nat := [1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 4]
def baseStart_2328183 : Nat := 118140960795 + 2328183 * 2 ^ 59
def prefixEnd_2328183 : Nat := 4983230072969 + 3 ^ 40 * 2328183 * 2
def baseEnd_2328183 : Nat := 1195476930626769707005387

theorem tailTrace_2328183 : CollatzResearch.WordTrace tailWord_2328183 prefixEnd_2328183 1195476930626769707005387 := by
  unfold tailWord_2328183
  simp only [CollatzResearch.WordTrace]
  refine ⟨84915810124398087845205203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56610540082932058563470135 84915810124398087845205203)
  ·
    refine ⟨127373715186597131767807805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84915810124398087845205203 127373715186597131767807805)
    ·
      refine ⟨47765143194973924412927927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127373715186597131767807805 47765143194973924412927927)
      ·
        refine ⟨71647714792460886619391891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47765143194973924412927927 71647714792460886619391891)
        ·
          refine ⟨107471572188691329929087837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71647714792460886619391891 107471572188691329929087837)
          ·
            refine ⟨40301839570759248723407939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107471572188691329929087837 40301839570759248723407939)
            ·
              refine ⟨60452759356138873085111909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40301839570759248723407939 60452759356138873085111909)
              ·
                refine ⟨11334892379276038703458483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60452759356138873085111909 11334892379276038703458483)
                ·
                  refine ⟨17002338568914058055187725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11334892379276038703458483 17002338568914058055187725)
                  ·
                    refine ⟨6375876963342771770695397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17002338568914058055187725 6375876963342771770695397)
                    ·
                      refine ⟨1195476930626769707005387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6375876963342771770695397 1195476930626769707005387)
                      ·
                        rfl

theorem cell23_2328183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_2328183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328183 prefixEnd_2328183 := by exact prefixLift 2328183
  have htrace : WordTrace (prefixWord ++ tailWord_2328183) baseStart_2328183 baseEnd_2328183 := by
    simpa [prefixWord, tailWord_2328183, baseEnd_2328183] using wordTrace_append hprefix tailTrace_2328183
  have hstable : (prefixWord ++ tailWord_2328183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328183).length < 2 ^ (prefixWord ++ tailWord_2328183).sum := by decide
  have hdescent : baseEnd_2328183 < baseStart_2328183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328213 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 1, 6, 4]
def baseStart_2328213 : Nat := 118140960795 + 2328213 * 2 ^ 59
def prefixEnd_2328213 : Nat := 4983230072969 + 3 ^ 40 * 2328213 * 2
def baseEnd_2328213 : Nat := 1195492335046404589630249

theorem tailTrace_2328213 : CollatzResearch.WordTrace tailWord_2328213 prefixEnd_2328213 1195492335046404589630249 := by
  unfold tailWord_2328213
  simp only [CollatzResearch.WordTrace]
  refine ⟨84916904314289402968797293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56611269542859601979198195 84916904314289402968797293)
  ·
    refine ⟨31843839117858526113298985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84916904314289402968797293 31843839117858526113298985)
    ·
      refine ⟨23882879338393894584974239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31843839117858526113298985 23882879338393894584974239)
      ·
        refine ⟨35824319007590841877461359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23882879338393894584974239 35824319007590841877461359)
        ·
          refine ⟨53736478511386262816192039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35824319007590841877461359 53736478511386262816192039)
          ·
            refine ⟨80604717767079394224288059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53736478511386262816192039 80604717767079394224288059)
            ·
              refine ⟨120907076650619091336432089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80604717767079394224288059 120907076650619091336432089)
              ·
                refine ⟨90680307487964318502324067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120907076650619091336432089 90680307487964318502324067)
                ·
                  refine ⟨136020461231946477753486101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90680307487964318502324067 136020461231946477753486101)
                  ·
                    refine ⟨6375959120247491144694661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 136020461231946477753486101 6375959120247491144694661)
                    ·
                      refine ⟨1195492335046404589630249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6375959120247491144694661 1195492335046404589630249)
                      ·
                        rfl

theorem cell23_2328213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_2328213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328213 prefixEnd_2328213 := by exact prefixLift 2328213
  have htrace : WordTrace (prefixWord ++ tailWord_2328213) baseStart_2328213 baseEnd_2328213 := by
    simpa [prefixWord, tailWord_2328213, baseEnd_2328213] using wordTrace_append hprefix tailTrace_2328213
  have hstable : (prefixWord ++ tailWord_2328213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328213).length < 2 ^ (prefixWord ++ tailWord_2328213).sum := by decide
  have hdescent : baseEnd_2328213 < baseStart_2328213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328227 : List Nat := [1, 1, 1, 4, 1, 1, 3, 6, 1, 4]
def baseStart_2328227 : Nat := 118140960795 + 2328227 * 2 ^ 59
def prefixEnd_2328227 : Nat := 4983230072969 + 3 ^ 40 * 2328227 * 2
def baseEnd_2328227 : Nat := 398499841258522511618395

theorem tailTrace_2328227 : CollatzResearch.WordTrace tailWord_2328227 prefixEnd_2328227 398499841258522511618395 := by
  unfold tailWord_2328227
  simp only [CollatzResearch.WordTrace]
  refine ⟨84917414936238683359806935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56611609957492455573204623 84917414936238683359806935)
  ·
    refine ⟨127376122404358025039710403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84917414936238683359806935 127376122404358025039710403)
    ·
      refine ⟨191064183606537037559565605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127376122404358025039710403 191064183606537037559565605)
      ·
        refine ⟨35824534426225694542418551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 191064183606537037559565605 35824534426225694542418551)
        ·
          refine ⟨53736801639338541813627827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35824534426225694542418551 53736801639338541813627827)
          ·
            refine ⟨80605202459007812720441741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53736801639338541813627827 80605202459007812720441741)
            ·
              refine ⟨30226950922127929770165653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80605202459007812720441741 30226950922127929770165653)
              ·
                refine ⟨1416888324474746707976515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30226950922127929770165653 1416888324474746707976515)
                ·
                  refine ⟨2125332486712120061964773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1416888324474746707976515 2125332486712120061964773)
                  ·
                    refine ⟨398499841258522511618395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2125332486712120061964773 398499841258522511618395)
                    ·
                      rfl

theorem cell23_2328227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 6, 1, 4].length) (baseStart_2328227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328227 prefixEnd_2328227 := by exact prefixLift 2328227
  have htrace : WordTrace (prefixWord ++ tailWord_2328227) baseStart_2328227 baseEnd_2328227 := by
    simpa [prefixWord, tailWord_2328227, baseEnd_2328227] using wordTrace_append hprefix tailTrace_2328227
  have hstable : (prefixWord ++ tailWord_2328227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328227).length < 2 ^ (prefixWord ++ tailWord_2328227).sum := by decide
  have hdescent : baseEnd_2328227 < baseStart_2328227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328243 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 6]
def baseStart_2328243 : Nat := 118140960795 + 2328243 * 2 ^ 59
def prefixEnd_2328243 : Nat := 4983230072969 + 3 ^ 40 * 2328243 * 2
def baseEnd_2328243 : Nat := 1195507739466039472255111

theorem tailTrace_2328243 : CollatzResearch.WordTrace tailWord_2328243 prefixEnd_2328243 1195507739466039472255111 := by
  unfold tailWord_2328243
  simp only [CollatzResearch.WordTrace]
  refine ⟨84917998504180718092389383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56611999002787145394926255 84917998504180718092389383)
  ·
    refine ⟨127376997756271077138584075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84917998504180718092389383 127376997756271077138584075)
    ·
      refine ⟨191065496634406615707876113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127376997756271077138584075 191065496634406615707876113)
      ·
        refine ⟨143299122475804961780907085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191065496634406615707876113 143299122475804961780907085)
        ·
          refine ⟨53737170928426860667840157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143299122475804961780907085 53737170928426860667840157)
          ·
            refine ⟨20151439098160072750440059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53737170928426860667840157 20151439098160072750440059)
            ·
              refine ⟨30227158647240109125660089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20151439098160072750440059 30227158647240109125660089)
              ·
                refine ⟨22670368985430081844245067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30227158647240109125660089 22670368985430081844245067)
                ·
                  refine ⟨34005553478145122766367601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22670368985430081844245067 34005553478145122766367601)
                  ·
                    refine ⟨25504165108608842074775701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34005553478145122766367601 25504165108608842074775701)
                    ·
                      refine ⟨1195507739466039472255111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25504165108608842074775701 1195507739466039472255111)
                      ·
                        rfl

theorem cell23_2328243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 6].length) (baseStart_2328243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328243 prefixEnd_2328243 := by exact prefixLift 2328243
  have htrace : WordTrace (prefixWord ++ tailWord_2328243) baseStart_2328243 baseEnd_2328243 := by
    simpa [prefixWord, tailWord_2328243, baseEnd_2328243] using wordTrace_append hprefix tailTrace_2328243
  have hstable : (prefixWord ++ tailWord_2328243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328243).length < 2 ^ (prefixWord ++ tailWord_2328243).sum := by decide
  have hdescent : baseEnd_2328243 < baseStart_2328243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328278 : List Nat := [5, 2, 1, 3, 1, 2, 1, 1, 3, 4]
def baseStart_2328278 : Nat := 118140960795 + 2328278 * 2 ^ 59
def prefixEnd_2328278 : Nat := 4983230072969 + 3 ^ 40 * 2328278 * 2
def baseEnd_2328278 : Nat := 398508570429648945105817

theorem tailTrace_2328278 : CollatzResearch.WordTrace tailWord_2328278 prefixEnd_2328278 398508570429648945105817 := by
  unfold tailWord_2328278
  simp only [CollatzResearch.WordTrace]
  refine ⟨5307454691190869941869593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56612850039369279379942325 5307454691190869941869593)
  ·
    refine ⟨3980591018393152456402195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5307454691190869941869593 3980591018393152456402195)
    ·
      refine ⟨5970886527589728684603293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3980591018393152456402195 5970886527589728684603293)
      ·
        refine ⟨2239082447846148256726235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5970886527589728684603293 2239082447846148256726235)
        ·
          refine ⟨3358623671769222385089353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2239082447846148256726235 3358623671769222385089353)
          ·
            refine ⟨2518967753826916788817015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3358623671769222385089353 2518967753826916788817015)
            ·
              refine ⟨3778451630740375183225523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2518967753826916788817015 3778451630740375183225523)
              ·
                refine ⟨5667677446110562774838285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3778451630740375183225523 5667677446110562774838285)
                ·
                  refine ⟨2125379042291461040564357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5667677446110562774838285 2125379042291461040564357)
                  ·
                    refine ⟨398508570429648945105817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2125379042291461040564357 398508570429648945105817)
                    ·
                      rfl

theorem cell23_2328278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_2328278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328278 prefixEnd_2328278 := by exact prefixLift 2328278
  have htrace : WordTrace (prefixWord ++ tailWord_2328278) baseStart_2328278 baseEnd_2328278 := by
    simpa [prefixWord, tailWord_2328278, baseEnd_2328278] using wordTrace_append hprefix tailTrace_2328278
  have hstable : (prefixWord ++ tailWord_2328278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328278).length < 2 ^ (prefixWord ++ tailWord_2328278).sum := by decide
  have hdescent : baseEnd_2328278 < baseStart_2328278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328291 : List Nat := [1, 1, 1, 7, 3, 1, 2, 1, 6]
def baseStart_2328291 : Nat := 118140960795 + 2328291 * 2 ^ 59
def prefixEnd_2328291 : Nat := 4983230072969 + 3 ^ 40 * 2328291 * 2
def baseEnd_2328291 : Nat := 132836931837495031606099

theorem tailTrace_2328291 : CollatzResearch.WordTrace tailWord_2328291 prefixEnd_2328291 132836931837495031606099 := by
  unfold tailWord_2328291
  simp only [CollatzResearch.WordTrace]
  refine ⟨84919749208006822290136727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56613166138671214860091151 84919749208006822290136727)
  ·
    refine ⟨127379623812010233435205091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84919749208006822290136727 127379623812010233435205091)
    ·
      refine ⟨191069435718015350152807637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127379623812010233435205091 191069435718015350152807637)
      ·
        refine ⟨4478189899640984769206429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 191069435718015350152807637 4478189899640984769206429)
        ·
          refine ⟨1679321212365369288452411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4478189899640984769206429 1679321212365369288452411)
          ·
            refine ⟨2518981818548053932678617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1679321212365369288452411 2518981818548053932678617)
            ·
              refine ⟨1889236363911040449508963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2518981818548053932678617 1889236363911040449508963)
              ·
                refine ⟨2833854545866560674263445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1889236363911040449508963 2833854545866560674263445)
                ·
                  refine ⟨132836931837495031606099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2833854545866560674263445 132836931837495031606099)
                  ·
                    rfl

theorem cell23_2328291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 6].length) (baseStart_2328291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328291 prefixEnd_2328291 := by exact prefixLift 2328291
  have htrace : WordTrace (prefixWord ++ tailWord_2328291) baseStart_2328291 baseEnd_2328291 := by
    simpa [prefixWord, tailWord_2328291, baseEnd_2328291] using wordTrace_append hprefix tailTrace_2328291
  have hstable : (prefixWord ++ tailWord_2328291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328291).length < 2 ^ (prefixWord ++ tailWord_2328291).sum := by decide
  have hdescent : baseEnd_2328291 < baseStart_2328291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328307 : List Nat := [1, 1, 1, 2, 2, 3, 5, 2, 1, 1, 4]
def baseStart_2328307 : Nat := 118140960795 + 2328307 * 2 ^ 59
def prefixEnd_2328307 : Nat := 4983230072969 + 3 ^ 40 * 2328307 * 2
def baseEnd_2328307 : Nat := 1195540602227927221854817

theorem tailTrace_2328307 : CollatzResearch.WordTrace tailWord_2328307 prefixEnd_2328307 1195540602227927221854817 := by
  unfold tailWord_2328307
  simp only [CollatzResearch.WordTrace]
  refine ⟨84920332775948857022719175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56613555183965904681812783 84920332775948857022719175)
  ·
    refine ⟨127380499163923285534078763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84920332775948857022719175 127380499163923285534078763)
    ·
      refine ⟨191070748745884928301118145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127380499163923285534078763 191070748745884928301118145)
      ·
        refine ⟨143303061559413696225838609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191070748745884928301118145 143303061559413696225838609)
        ·
          refine ⟨107477296169560272169378957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143303061559413696225838609 107477296169560272169378957)
          ·
            refine ⟨40303986063585102063517109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107477296169560272169378957 40303986063585102063517109)
            ·
              refine ⟨3778498693461103318454729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40303986063585102063517109 3778498693461103318454729)
              ·
                refine ⟨2833874020095827488841047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3778498693461103318454729 2833874020095827488841047)
                ·
                  refine ⟨4250811030143741233261571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2833874020095827488841047 4250811030143741233261571)
                  ·
                    refine ⟨6376216545215611849892357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4250811030143741233261571 6376216545215611849892357)
                    ·
                      refine ⟨1195540602227927221854817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6376216545215611849892357 1195540602227927221854817)
                      ·
                        rfl

theorem cell23_2328307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 1, 4].length) (baseStart_2328307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328307 prefixEnd_2328307 := by exact prefixLift 2328307
  have htrace : WordTrace (prefixWord ++ tailWord_2328307) baseStart_2328307 baseEnd_2328307 := by
    simpa [prefixWord, tailWord_2328307, baseEnd_2328307] using wordTrace_append hprefix tailTrace_2328307
  have hstable : (prefixWord ++ tailWord_2328307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328307).length < 2 ^ (prefixWord ++ tailWord_2328307).sum := by decide
  have hdescent : baseEnd_2328307 < baseStart_2328307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328320 : List Nat := [2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 4]
def baseStart_2328320 : Nat := 118140960795 + 2328320 * 2 ^ 59
def prefixEnd_2328320 : Nat := 4983230072969 + 3 ^ 40 * 2328320 * 2
def baseEnd_2328320 : Nat := 1195547277476435670992257

theorem tailTrace_2328320 : CollatzResearch.WordTrace tailWord_2328320 prefixEnd_2328320 1195547277476435670992257 := by
  unfold tailWord_2328320
  simp only [CollatzResearch.WordTrace]
  refine ⟨42460403462450880121471207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56613871283267840161961609 42460403462450880121471207)
  ·
    refine ⟨63690605193676320182206811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42460403462450880121471207 63690605193676320182206811)
    ·
      refine ⟨95535907790514480273310217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63690605193676320182206811 95535907790514480273310217)
      ·
        refine ⟨71651930842885860204982663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95535907790514480273310217 71651930842885860204982663)
        ·
          refine ⟨107477896264328790307473995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71651930842885860204982663 107477896264328790307473995)
          ·
            refine ⟨161216844396493185461210993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107477896264328790307473995 161216844396493185461210993)
            ·
              refine ⟨120912633297369889095908245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161216844396493185461210993 120912633297369889095908245)
              ·
                refine ⟨5667779685814213551370699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 120912633297369889095908245 5667779685814213551370699)
                ·
                  refine ⟨8501669528721320327056049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5667779685814213551370699 8501669528721320327056049)
                  ·
                    refine ⟨6376252146540990245292037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8501669528721320327056049 6376252146540990245292037)
                    ·
                      refine ⟨1195547277476435670992257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6376252146540990245292037 1195547277476435670992257)
                      ·
                        rfl

theorem cell23_2328320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 4].length) (baseStart_2328320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328320 prefixEnd_2328320 := by exact prefixLift 2328320
  have htrace : WordTrace (prefixWord ++ tailWord_2328320) baseStart_2328320 baseEnd_2328320 := by
    simpa [prefixWord, tailWord_2328320, baseEnd_2328320] using wordTrace_append hprefix tailTrace_2328320
  have hstable : (prefixWord ++ tailWord_2328320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328320).length < 2 ^ (prefixWord ++ tailWord_2328320).sum := by decide
  have hdescent : baseEnd_2328320 < baseStart_2328320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328357 : List Nat := [1, 3, 1, 2, 3, 2, 1, 3, 1, 3, 3]
def baseStart_2328357 : Nat := 118140960795 + 2328357 * 2 ^ 59
def prefixEnd_2328357 : Nat := 4983230072969 + 3 ^ 40 * 2328357 * 2
def baseEnd_2328357 : Nat := 1195566276260652026229587

theorem tailTrace_2328357 : CollatzResearch.WordTrace tailWord_2328357 prefixEnd_2328357 1195566276260652026229587 := by
  unfold tailWord_2328357
  simp only [CollatzResearch.WordTrace]
  refine ⟨84922156425767715562039325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56614770950511810374692883 84922156425767715562039325)
  ·
    refine ⟨31845808659662893335764747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84922156425767715562039325 31845808659662893335764747)
    ·
      refine ⟨47768712989494340003647121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31845808659662893335764747 47768712989494340003647121)
      ·
        refine ⟨35826534742120755002735341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47768712989494340003647121 35826534742120755002735341)
        ·
          refine ⟨13434950528295283126025753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35826534742120755002735341 13434950528295283126025753)
          ·
            refine ⟨10076212896221462344519315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13434950528295283126025753 10076212896221462344519315)
            ·
              refine ⟨15114319344332193516778973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10076212896221462344519315 15114319344332193516778973)
              ·
                refine ⟨5667869754124572568792115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15114319344332193516778973 5667869754124572568792115)
                ·
                  refine ⟨8501804631186858853188173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5667869754124572568792115 8501804631186858853188173)
                  ·
                    refine ⟨3188176736695072069945565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8501804631186858853188173 3188176736695072069945565)
                    ·
                      refine ⟨1195566276260652026229587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3188176736695072069945565 1195566276260652026229587)
                      ·
                        rfl

theorem cell23_2328357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_2328357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328357 prefixEnd_2328357 := by exact prefixLift 2328357
  have htrace : WordTrace (prefixWord ++ tailWord_2328357) baseStart_2328357 baseEnd_2328357 := by
    simpa [prefixWord, tailWord_2328357, baseEnd_2328357] using wordTrace_append hprefix tailTrace_2328357
  have hstable : (prefixWord ++ tailWord_2328357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328357).length < 2 ^ (prefixWord ++ tailWord_2328357).sum := by decide
  have hdescent : baseEnd_2328357 < baseStart_2328357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328400 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 5]
def baseStart_2328400 : Nat := 118140960795 + 2328400 * 2 ^ 59
def prefixEnd_2328400 : Nat := 4983230072969 + 3 ^ 40 * 2328400 * 2
def baseEnd_2328400 : Nat := 1195588355928795357991889

theorem tailTrace_2328400 : CollatzResearch.WordTrace tailWord_2328400 prefixEnd_2328400 1195588355928795357991889 := by
  unfold tailWord_2328400
  simp only [CollatzResearch.WordTrace]
  refine ⟨42461862382305966952927327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56615816509741289270569769 42461862382305966952927327)
  ·
    refine ⟨63692793573458950429390991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42461862382305966952927327 63692793573458950429390991)
    ·
      refine ⟨95539190360188425644086487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63692793573458950429390991 95539190360188425644086487)
      ·
        refine ⟨143308785540282638466129731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95539190360188425644086487 143308785540282638466129731)
        ·
          refine ⟨214963178310423957699194597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143308785540282638466129731 214963178310423957699194597)
          ·
            refine ⟨40305595933204492068598987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 214963178310423957699194597 40305595933204492068598987)
            ·
              refine ⟨60458393899806738102898481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40305595933204492068598987 60458393899806738102898481)
              ·
                refine ⟨45343795424855053577173861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60458393899806738102898481 45343795424855053577173861)
                ·
                  refine ⟨8501961642160322545720099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45343795424855053577173861 8501961642160322545720099)
                  ·
                    refine ⟨12752942463240483818580149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8501961642160322545720099 12752942463240483818580149)
                    ·
                      refine ⟨1195588355928795357991889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12752942463240483818580149 1195588355928795357991889)
                      ·
                        rfl

theorem cell23_2328400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 5].length) (baseStart_2328400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328400 prefixEnd_2328400 := by exact prefixLift 2328400
  have htrace : WordTrace (prefixWord ++ tailWord_2328400) baseStart_2328400 baseEnd_2328400 := by
    simpa [prefixWord, tailWord_2328400, baseEnd_2328400] using wordTrace_append hprefix tailTrace_2328400
  have hstable : (prefixWord ++ tailWord_2328400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328400).length < 2 ^ (prefixWord ++ tailWord_2328400).sum := by decide
  have hdescent : baseEnd_2328400 < baseStart_2328400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328418 : List Nat := [3, 3, 2, 1, 2, 2, 2, 2, 1, 3, 2]
def baseStart_2328418 : Nat := 118140960795 + 2328418 * 2 ^ 59
def prefixEnd_2328418 : Nat := 4983230072969 + 3 ^ 40 * 2328418 * 2
def baseEnd_2328418 : Nat := 1195597598580576287566807

theorem tailTrace_2328418 : CollatzResearch.WordTrace tailWord_2328418 prefixEnd_2328418 1195597598580576287566807 := by
  unfold tailWord_2328418
  simp only [CollatzResearch.WordTrace]
  refine ⟨21231095319636680745002477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56616254185697815320006605 21231095319636680745002477)
  ·
    refine ⟨7961660744863755279375929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21231095319636680745002477 7961660744863755279375929)
    ·
      refine ⟨5971245558647816459531947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7961660744863755279375929 5971245558647816459531947)
      ·
        refine ⟨8956868337971724689297921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5971245558647816459531947 8956868337971724689297921)
        ·
          refine ⟨6717651253478793516973441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8956868337971724689297921 6717651253478793516973441)
          ·
            refine ⟨5038238440109095137730081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6717651253478793516973441 5038238440109095137730081)
            ·
              refine ⟨3778678830081821353297561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5038238440109095137730081 3778678830081821353297561)
              ·
                refine ⟨2834009122561366014973171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3778678830081821353297561 2834009122561366014973171)
                ·
                  refine ⟨4251013683842049022459757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2834009122561366014973171 4251013683842049022459757)
                  ·
                    refine ⟨1594130131440768383422409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4251013683842049022459757 1594130131440768383422409)
                    ·
                      refine ⟨1195597598580576287566807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1594130131440768383422409 1195597598580576287566807)
                      ·
                        rfl

theorem cell23_2328418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_2328418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328418 prefixEnd_2328418 := by exact prefixLift 2328418
  have htrace : WordTrace (prefixWord ++ tailWord_2328418) baseStart_2328418 baseEnd_2328418 := by
    simpa [prefixWord, tailWord_2328418, baseEnd_2328418] using wordTrace_append hprefix tailTrace_2328418
  have hstable : (prefixWord ++ tailWord_2328418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328418).length < 2 ^ (prefixWord ++ tailWord_2328418).sum := by decide
  have hdescent : baseEnd_2328418 < baseStart_2328418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328484 : List Nat := [2, 3, 1, 2, 1, 4, 2, 1, 2, 5]
def baseStart_2328484 : Nat := 118140960795 + 2328484 * 2 ^ 59
def prefixEnd_2328484 : Nat := 4983230072969 + 3 ^ 40 * 2328484 * 2
def baseEnd_2328484 : Nat := 398543829434591009780501

theorem tailTrace_2328484 : CollatzResearch.WordTrace tailWord_2328484 prefixEnd_2328484 398543829434591009780501 := by
  unfold tailWord_2328484
  simp only [CollatzResearch.WordTrace]
  refine ⟨42463394248153808125956253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56617858997538410834608337 42463394248153808125956253)
  ·
    refine ⟨15923772843057678047233595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42463394248153808125956253 15923772843057678047233595)
    ·
      refine ⟨23885659264586517070850393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15923772843057678047233595 23885659264586517070850393)
      ·
        refine ⟨17914244448439887803137795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23885659264586517070850393 17914244448439887803137795)
        ·
          refine ⟨26871366672659831704706693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17914244448439887803137795 26871366672659831704706693)
          ·
            refine ⟨5038381251123718444632505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26871366672659831704706693 5038381251123718444632505)
            ·
              refine ⟨3778785938342788833474379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5038381251123718444632505 3778785938342788833474379)
              ·
                refine ⟨5668178907514183250211569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3778785938342788833474379 5668178907514183250211569)
                ·
                  refine ⟨4251134180635637437658677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5668178907514183250211569 4251134180635637437658677)
                  ·
                    refine ⟨398543829434591009780501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4251134180635637437658677 398543829434591009780501)
                    ·
                      rfl

theorem cell23_2328484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_2328484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328484 prefixEnd_2328484 := by exact prefixLift 2328484
  have htrace : WordTrace (prefixWord ++ tailWord_2328484) baseStart_2328484 baseEnd_2328484 := by
    simpa [prefixWord, tailWord_2328484, baseEnd_2328484] using wordTrace_append hprefix tailTrace_2328484
  have hstable : (prefixWord ++ tailWord_2328484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328484).length < 2 ^ (prefixWord ++ tailWord_2328484).sum := by decide
  have hdescent : baseEnd_2328484 < baseStart_2328484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328504 : List Nat := [2, 1, 2, 1, 2, 3, 2, 2, 2, 4, 2]
def baseStart_2328504 : Nat := 118140960795 + 2328504 * 2 ^ 59
def prefixEnd_2328504 : Nat := 4983230072969 + 3 ^ 40 * 2328504 * 2
def baseEnd_2328504 : Nat := 1195641757916862951091411

theorem tailTrace_2328504 : CollatzResearch.WordTrace tailWord_2328504 prefixEnd_2328504 1195641757916862951091411 := by
  unfold tailWord_2328504
  simp only [CollatzResearch.WordTrace]
  refine ⟨42463758978117579833820283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56618345304156773111760377 42463758978117579833820283)
  ·
    refine ⟨63695638467176369750730425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42463758978117579833820283 63695638467176369750730425)
    ·
      refine ⟨47771728850382277313047819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63695638467176369750730425 47771728850382277313047819)
      ·
        refine ⟨71657593275573415969571729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47771728850382277313047819 71657593275573415969571729)
        ·
          refine ⟨53743194956680061977178797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71657593275573415969571729 53743194956680061977178797)
          ·
            refine ⟨20153698108755023241442049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53743194956680061977178797 20153698108755023241442049)
            ·
              refine ⟨15115273581566267431081537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20153698108755023241442049 15115273581566267431081537)
              ·
                refine ⟨11336455186174700573311153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15115273581566267431081537 11336455186174700573311153)
                ·
                  refine ⟨8502341389631025429983365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11336455186174700573311153 8502341389631025429983365)
                  ·
                    refine ⟨1594189010555817268121881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8502341389631025429983365 1594189010555817268121881)
                    ·
                      refine ⟨1195641757916862951091411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1594189010555817268121881 1195641757916862951091411)
                      ·
                        rfl

theorem cell23_2328504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 2, 4, 2].length) (baseStart_2328504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328504 prefixEnd_2328504 := by exact prefixLift 2328504
  have htrace : WordTrace (prefixWord ++ tailWord_2328504) baseStart_2328504 baseEnd_2328504 := by
    simpa [prefixWord, tailWord_2328504, baseEnd_2328504] using wordTrace_append hprefix tailTrace_2328504
  have hstable : (prefixWord ++ tailWord_2328504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328504).length < 2 ^ (prefixWord ++ tailWord_2328504).sum := by decide
  have hdescent : baseEnd_2328504 < baseStart_2328504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328527 : List Nat := [1, 1, 2, 1, 1, 5, 1, 5, 6]
def baseStart_2328527 : Nat := 118140960795 + 2328527 * 2 ^ 59
def prefixEnd_2328527 : Nat := 4983230072969 + 3 ^ 40 * 2328527 * 2
def baseEnd_2328527 : Nat := 132850396441324040122645

theorem tailTrace_2328527 : CollatzResearch.WordTrace tailWord_2328527 prefixEnd_2328527 132850396441324040122645 := by
  unfold tailWord_2328527
  simp only [CollatzResearch.WordTrace]
  refine ⟨84928356835151834595727835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56618904556767889730485223 84928356835151834595727835)
  ·
    refine ⟨127392535252727751893591753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84928356835151834595727835 127392535252727751893591753)
    ·
      refine ⟨95544401439545813920193815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127392535252727751893591753 95544401439545813920193815)
      ·
        refine ⟨143316602159318720880290723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95544401439545813920193815 143316602159318720880290723)
        ·
          refine ⟨214974903238978081320436085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143316602159318720880290723 214974903238978081320436085)
          ·
            refine ⟨20153897178654195123790883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 214974903238978081320436085 20153897178654195123790883)
            ·
              refine ⟨30230845767981292685686325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20153897178654195123790883 30230845767981292685686325)
              ·
                refine ⟨2834141790748246189283093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30230845767981292685686325 2834141790748246189283093)
                ·
                  refine ⟨132850396441324040122645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2834141790748246189283093 132850396441324040122645)
                  ·
                    rfl

theorem cell23_2328527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 6].length) (baseStart_2328527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328527 prefixEnd_2328527 := by exact prefixLift 2328527
  have htrace : WordTrace (prefixWord ++ tailWord_2328527) baseStart_2328527 baseEnd_2328527 := by
    simpa [prefixWord, tailWord_2328527, baseEnd_2328527] using wordTrace_append hprefix tailTrace_2328527
  have hstable : (prefixWord ++ tailWord_2328527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328527).length < 2 ^ (prefixWord ++ tailWord_2328527).sum := by decide
  have hdescent : baseEnd_2328527 < baseStart_2328527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328538 : List Nat := [3, 1, 1, 2, 6, 1, 1, 1, 2, 1, 4]
def baseStart_2328538 : Nat := 118140960795 + 2328538 * 2 ^ 59
def prefixEnd_2328538 : Nat := 4983230072969 + 3 ^ 40 * 2328538 * 2
def baseEnd_2328538 : Nat := 1195659216259115818066255

theorem tailTrace_2328538 : CollatzResearch.WordTrace tailWord_2328538 prefixEnd_2328538 1195659216259115818066255 := by
  unfold tailWord_2328538
  simp only [CollatzResearch.WordTrace]
  refine ⟨21232189509527995868594567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56619172025407988982918845 21232189509527995868594567)
  ·
    refine ⟨31848284264291993802891851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21232189509527995868594567 31848284264291993802891851)
    ·
      refine ⟨47772426396437990704337777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31848284264291993802891851 47772426396437990704337777)
      ·
        refine ⟨35829319797328493028253333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47772426396437990704337777 35829319797328493028253333)
        ·
          refine ⟨1679499365499773110699375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 35829319797328493028253333 1679499365499773110699375)
          ·
            refine ⟨2519249048249659666049063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1679499365499773110699375 2519249048249659666049063)
            ·
              refine ⟨3778873572374489499073595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2519249048249659666049063 3778873572374489499073595)
              ·
                refine ⟨5668310358561734248610393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3778873572374489499073595 5668310358561734248610393)
                ·
                  refine ⟨4251232768921300686457795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5668310358561734248610393 4251232768921300686457795)
                  ·
                    refine ⟨6376849153381951029686693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4251232768921300686457795 6376849153381951029686693)
                    ·
                      refine ⟨1195659216259115818066255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6376849153381951029686693 1195659216259115818066255)
                      ·
                        rfl

theorem cell23_2328538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 2, 1, 4].length) (baseStart_2328538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328538 prefixEnd_2328538 := by exact prefixLift 2328538
  have htrace : WordTrace (prefixWord ++ tailWord_2328538) baseStart_2328538 baseEnd_2328538 := by
    simpa [prefixWord, tailWord_2328538, baseEnd_2328538] using wordTrace_append hprefix tailTrace_2328538
  have hstable : (prefixWord ++ tailWord_2328538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328538).length < 2 ^ (prefixWord ++ tailWord_2328538).sum := by decide
  have hdescent : baseEnd_2328538 < baseStart_2328538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328541 : List Nat := [1, 4, 3, 1, 3, 1, 1, 1, 1, 4, 3]
def baseStart_2328541 : Nat := 118140960795 + 2328541 * 2 ^ 59
def prefixEnd_2328541 : Nat := 4983230072969 + 3 ^ 40 * 2328541 * 2
def baseEnd_2328541 : Nat := 1195660756701079306328741

theorem tailTrace_2328541 : CollatzResearch.WordTrace tailWord_2328541 prefixEnd_2328541 1195660756701079306328741 := by
  unfold tailWord_2328541
  simp only [CollatzResearch.WordTrace]
  refine ⟨84928867457101114986737477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56619244971400743324491651 84928867457101114986737477)
  ·
    refine ⟨15924162648206459060013277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84928867457101114986737477 15924162648206459060013277)
    ·
      refine ⟨5971560993077422147504979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15924162648206459060013277 5971560993077422147504979)
      ·
        refine ⟨8957341489616133221257469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5971560993077422147504979 8957341489616133221257469)
        ·
          refine ⟨3359003058606049957971551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8957341489616133221257469 3359003058606049957971551)
          ·
            refine ⟨5038504587909074936957327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3359003058606049957971551 5038504587909074936957327)
            ·
              refine ⟨7557756881863612405435991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5038504587909074936957327 7557756881863612405435991)
              ·
                refine ⟨11336635322795418608153987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7557756881863612405435991 11336635322795418608153987)
                ·
                  refine ⟨17004952984193127912230981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11336635322795418608153987 17004952984193127912230981)
                  ·
                    refine ⟨3188428684536211483543309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17004952984193127912230981 3188428684536211483543309)
                    ·
                      refine ⟨1195660756701079306328741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3188428684536211483543309 1195660756701079306328741)
                      ·
                        rfl

theorem cell23_2328541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_2328541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328541 prefixEnd_2328541 := by exact prefixLift 2328541
  have htrace : WordTrace (prefixWord ++ tailWord_2328541) baseStart_2328541 baseEnd_2328541 := by
    simpa [prefixWord, tailWord_2328541, baseEnd_2328541] using wordTrace_append hprefix tailTrace_2328541
  have hstable : (prefixWord ++ tailWord_2328541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328541).length < 2 ^ (prefixWord ++ tailWord_2328541).sum := by decide
  have hdescent : baseEnd_2328541 < baseStart_2328541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328561 : List Nat := [1, 2, 2, 2, 5, 2, 1, 2, 6]
def baseStart_2328561 : Nat := 118140960795 + 2328561 * 2 ^ 59
def prefixEnd_2328561 : Nat := 4983230072969 + 3 ^ 40 * 2328561 * 2
def baseEnd_2328561 : Nat := 132852336257129914230961

theorem tailTrace_2328561 : CollatzResearch.WordTrace tailWord_2328561 prefixEnd_2328561 132852336257129914230961 := by
  unfold tailWord_2328561
  simp only [CollatzResearch.WordTrace]
  refine ⟨84929596917028658402465537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56619731278019105601643691 84929596917028658402465537)
  ·
    refine ⟨63697197687771493801849153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84929596917028658402465537 63697197687771493801849153)
    ·
      refine ⟨47772898265828620351386865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63697197687771493801849153 47772898265828620351386865)
      ·
        refine ⟨35829673699371465263540149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47772898265828620351386865 35829673699371465263540149)
        ·
          refine ⟨3359031909316074868456889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35829673699371465263540149 3359031909316074868456889)
          ·
            refine ⟨2519273931987056151342667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3359031909316074868456889 2519273931987056151342667)
            ·
              refine ⟨3778910897980584227014001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2519273931987056151342667 3778910897980584227014001)
              ·
                refine ⟨2834183173485438170260501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3778910897980584227014001 2834183173485438170260501)
                ·
                  refine ⟨132852336257129914230961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2834183173485438170260501 132852336257129914230961)
                  ·
                    rfl

theorem cell23_2328561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 6].length) (baseStart_2328561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328561 prefixEnd_2328561 := by exact prefixLift 2328561
  have htrace : WordTrace (prefixWord ++ tailWord_2328561) baseStart_2328561 baseEnd_2328561 := by
    simpa [prefixWord, tailWord_2328561, baseEnd_2328561] using wordTrace_append hprefix tailTrace_2328561
  have hstable : (prefixWord ++ tailWord_2328561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328561).length < 2 ^ (prefixWord ++ tailWord_2328561).sum := by decide
  have hdescent : baseEnd_2328561 < baseStart_2328561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328605 : List Nat := [1, 4, 2, 2, 2, 1, 3, 3, 1, 1, 3]
def baseStart_2328605 : Nat := 118140960795 + 2328605 * 2 ^ 59
def prefixEnd_2328605 : Nat := 4983230072969 + 3 ^ 40 * 2328605 * 2
def baseEnd_2328605 : Nat := 1195693619462967055928447

theorem tailTrace_2328605 : CollatzResearch.WordTrace tailWord_2328605 prefixEnd_2328605 1195693619462967055928447 := by
  unfold tailWord_2328605
  simp only [CollatzResearch.WordTrace]
  refine ⟨84931201728869253917067269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56620801152579502611378179 84931201728869253917067269)
  ·
    refine ⟨15924600324162985109450113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84931201728869253917067269 15924600324162985109450113)
    ·
      refine ⟨11943450243122238832087585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15924600324162985109450113 11943450243122238832087585)
      ·
        refine ⟨8957587682341679124065689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11943450243122238832087585 8957587682341679124065689)
        ·
          refine ⟨6718190761756259343049267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8957587682341679124065689 6718190761756259343049267)
          ·
            refine ⟨10077286142634389014573901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6718190761756259343049267 10077286142634389014573901)
            ·
              refine ⟨3778982303487895880465213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10077286142634389014573901 3778982303487895880465213)
              ·
                refine ⟨1417118363807960955174455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3778982303487895880465213 1417118363807960955174455)
                ·
                  refine ⟨2125677545711941432761683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1417118363807960955174455 2125677545711941432761683)
                  ·
                    refine ⟨3188516318567912149142525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2125677545711941432761683 3188516318567912149142525)
                    ·
                      refine ⟨1195693619462967055928447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3188516318567912149142525 1195693619462967055928447)
                      ·
                        rfl

theorem cell23_2328605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_2328605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328605 prefixEnd_2328605 := by exact prefixLift 2328605
  have htrace : WordTrace (prefixWord ++ tailWord_2328605) baseStart_2328605 baseEnd_2328605 := by
    simpa [prefixWord, tailWord_2328605, baseEnd_2328605] using wordTrace_append hprefix tailTrace_2328605
  have hstable : (prefixWord ++ tailWord_2328605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328605).length < 2 ^ (prefixWord ++ tailWord_2328605).sum := by decide
  have hdescent : baseEnd_2328605 < baseStart_2328605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328615 : List Nat := [1, 1, 7, 1, 2, 1, 1, 2, 2, 3, 2]
def baseStart_2328615 : Nat := 118140960795 + 2328615 * 2 ^ 59
def prefixEnd_2328615 : Nat := 4983230072969 + 3 ^ 40 * 2328615 * 2
def baseEnd_2328615 : Nat := 1195698754269512016803401

theorem tailTrace_2328615 : CollatzResearch.WordTrace tailWord_2328615 prefixEnd_2328615 1195698754269512016803401 := by
  unfold tailWord_2328615
  simp only [CollatzResearch.WordTrace]
  refine ⟨84931566458833025624931299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56621044305888683749954199 84931566458833025624931299)
  ·
    refine ⟨127397349688249538437396949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84931566458833025624931299 127397349688249538437396949)
    ·
      refine ⟨2985875383318348557126491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 127397349688249538437396949 2985875383318348557126491)
      ·
        refine ⟨4478813074977522835689737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2985875383318348557126491 4478813074977522835689737)
        ·
          refine ⟨3359109806233142126767303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4478813074977522835689737 3359109806233142126767303)
          ·
            refine ⟨5038664709349713190150955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3359109806233142126767303 5038664709349713190150955)
            ·
              refine ⟨7557997064024569785226433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5038664709349713190150955 7557997064024569785226433)
              ·
                refine ⟨5668497798018427338919825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7557997064024569785226433 5668497798018427338919825)
                ·
                  refine ⟨4251373348513820504189869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5668497798018427338919825 4251373348513820504189869)
                  ·
                    refine ⟨1594265005692682689071201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4251373348513820504189869 1594265005692682689071201)
                    ·
                      refine ⟨1195698754269512016803401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1594265005692682689071201 1195698754269512016803401)
                      ·
                        rfl

theorem cell23_2328615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_2328615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328615 prefixEnd_2328615 := by exact prefixLift 2328615
  have htrace : WordTrace (prefixWord ++ tailWord_2328615) baseStart_2328615 baseEnd_2328615 := by
    simpa [prefixWord, tailWord_2328615, baseEnd_2328615] using wordTrace_append hprefix tailTrace_2328615
  have hstable : (prefixWord ++ tailWord_2328615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328615).length < 2 ^ (prefixWord ++ tailWord_2328615).sum := by decide
  have hdescent : baseEnd_2328615 < baseStart_2328615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328622 : List Nat := [4, 1, 3, 1, 1, 3, 3, 2, 1, 1, 3]
def baseStart_2328622 : Nat := 118140960795 + 2328622 * 2 ^ 59
def prefixEnd_2328622 : Nat := 4983230072969 + 3 ^ 40 * 2328622 * 2
def baseEnd_2328622 : Nat := 1195702348634093489415869

theorem tailTrace_2328622 : CollatzResearch.WordTrace tailWord_2328622 prefixEnd_2328622 1195702348634093489415869 := by
  unfold tailWord_2328622
  simp only [CollatzResearch.WordTrace]
  refine ⟨10616477721225958227554515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56621214513205110546957413 10616477721225958227554515)
  ·
    refine ⟨15924716581838937341331773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10616477721225958227554515 15924716581838937341331773)
    ·
      refine ⟨5971768718189601502999415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15924716581838937341331773 5971768718189601502999415)
      ·
        refine ⟨8957653077284402254499123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5971768718189601502999415 8957653077284402254499123)
        ·
          refine ⟨13436479615926603381748685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8957653077284402254499123 13436479615926603381748685)
          ·
            refine ⟨5038679855972476268155757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13436479615926603381748685 5038679855972476268155757)
            ·
              refine ⟨1889504945989678600558409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5038679855972476268155757 1889504945989678600558409)
              ·
                refine ⟨1417128709492258950418807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1889504945989678600558409 1417128709492258950418807)
                ·
                  refine ⟨2125693064238388425628211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1417128709492258950418807 2125693064238388425628211)
                  ·
                    refine ⟨3188539596357582638442317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2125693064238388425628211 3188539596357582638442317)
                    ·
                      refine ⟨1195702348634093489415869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3188539596357582638442317 1195702348634093489415869)
                      ·
                        rfl

theorem cell23_2328622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_2328622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328622 prefixEnd_2328622 := by exact prefixLift 2328622
  have htrace : WordTrace (prefixWord ++ tailWord_2328622) baseStart_2328622 baseEnd_2328622 := by
    simpa [prefixWord, tailWord_2328622, baseEnd_2328622] using wordTrace_append hprefix tailTrace_2328622
  have hstable : (prefixWord ++ tailWord_2328622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328622).length < 2 ^ (prefixWord ++ tailWord_2328622).sum := by decide
  have hdescent : baseEnd_2328622 < baseStart_2328622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328661 : List Nat := [1, 3, 2, 2, 1, 4, 1, 2, 1, 3, 3]
def baseStart_2328661 : Nat := 118140960795 + 2328661 * 2 ^ 59
def prefixEnd_2328661 : Nat := 4983230072969 + 3 ^ 40 * 2328661 * 2
def baseEnd_2328661 : Nat := 1195722374379618836828189

theorem tailTrace_2328661 : CollatzResearch.WordTrace tailWord_2328661 prefixEnd_2328661 1195722374379618836828189 := by
  unfold tailWord_2328661
  simp only [CollatzResearch.WordTrace]
  refine ⟨84933244216666375481105837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56622162811110916987403891 84933244216666375481105837)
  ·
    refine ⟨31849966581249890805414689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84933244216666375481105837 31849966581249890805414689)
    ·
      refine ⟨23887474935937418104061017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31849966581249890805414689 23887474935937418104061017)
      ·
        refine ⟨17915606201953063578045763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23887474935937418104061017 17915606201953063578045763)
        ·
          refine ⟨26873409302929595367068645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17915606201953063578045763 26873409302929595367068645)
          ·
            refine ⟨5038764244299299131325371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26873409302929595367068645 5038764244299299131325371)
            ·
              refine ⟨7558146366448948696988057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5038764244299299131325371 7558146366448948696988057)
              ·
                refine ⟨5668609774836711522741043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7558146366448948696988057 5668609774836711522741043)
                ·
                  refine ⟨8502914662255067284111565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5668609774836711522741043 8502914662255067284111565)
                  ·
                    refine ⟨3188592998345650231541837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8502914662255067284111565 3188592998345650231541837)
                    ·
                      refine ⟨1195722374379618836828189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3188592998345650231541837 1195722374379618836828189)
                      ·
                        rfl

theorem cell23_2328661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_2328661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328661 prefixEnd_2328661 := by exact prefixLift 2328661
  have htrace : WordTrace (prefixWord ++ tailWord_2328661) baseStart_2328661 baseEnd_2328661 := by
    simpa [prefixWord, tailWord_2328661, baseEnd_2328661] using wordTrace_append hprefix tailTrace_2328661
  have hstable : (prefixWord ++ tailWord_2328661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328661).length < 2 ^ (prefixWord ++ tailWord_2328661).sum := by decide
  have hdescent : baseEnd_2328661 < baseStart_2328661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328662 : List Nat := [5, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4]
def baseStart_2328662 : Nat := 118140960795 + 2328662 * 2 ^ 59
def prefixEnd_2328662 : Nat := 4983230072969 + 3 ^ 40 * 2328662 * 2
def baseEnd_2328662 : Nat := 1195722887860273332915685

theorem tailTrace_2328662 : CollatzResearch.WordTrace tailWord_2328662 prefixEnd_2328662 1195722887860273332915685 := by
  unfold tailWord_2328662
  simp only [CollatzResearch.WordTrace]
  refine ⟨5308330043103922040743265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56622187126441835101261493 5308330043103922040743265)
  ·
    refine ⟨3981247532327941530557449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5308330043103922040743265 3981247532327941530557449)
    ·
      refine ⟨2985935649245956147918087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3981247532327941530557449 2985935649245956147918087)
      ·
        refine ⟨4478903473868934221877131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2985935649245956147918087 4478903473868934221877131)
        ·
          refine ⟨6718355210803401332815697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4478903473868934221877131 6718355210803401332815697)
          ·
            refine ⟨5038766408102550999611773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6718355210803401332815697 5038766408102550999611773)
            ·
              refine ⟨1889537403038456624854415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5038766408102550999611773 1889537403038456624854415)
              ·
                refine ⟨2834306104557684937281623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1889537403038456624854415 2834306104557684937281623)
                ·
                  refine ⟨4251459156836527405922435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2834306104557684937281623 4251459156836527405922435)
                  ·
                    refine ⟨6377188735254791108883653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4251459156836527405922435 6377188735254791108883653)
                    ·
                      refine ⟨1195722887860273332915685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6377188735254791108883653 1195722887860273332915685)
                      ·
                        rfl

theorem cell23_2328662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_2328662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328662 prefixEnd_2328662 := by exact prefixLift 2328662
  have htrace : WordTrace (prefixWord ++ tailWord_2328662) baseStart_2328662 baseEnd_2328662 := by
    simpa [prefixWord, tailWord_2328662, baseEnd_2328662] using wordTrace_append hprefix tailTrace_2328662
  have hstable : (prefixWord ++ tailWord_2328662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328662).length < 2 ^ (prefixWord ++ tailWord_2328662).sum := by decide
  have hdescent : baseEnd_2328662 < baseStart_2328662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328684 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 4]
def baseStart_2328684 : Nat := 118140960795 + 2328684 * 2 ^ 59
def prefixEnd_2328684 : Nat := 4983230072969 + 3 ^ 40 * 2328684 * 2
def baseEnd_2328684 : Nat := 1195734184434672246840583

theorem tailTrace_2328684 : CollatzResearch.WordTrace tailWord_2328684 prefixEnd_2328684 1195734184434672246840583 := by
  unfold tailWord_2328684
  simp only [CollatzResearch.WordTrace]
  refine ⟨42467041547791525204596553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56622722063722033606128737 42467041547791525204596553)
  ·
    refine ⟨31850281160843643903447415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42467041547791525204596553 31850281160843643903447415)
    ·
      refine ⟨47775421741265465855171123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31850281160843643903447415 47775421741265465855171123)
      ·
        refine ⟨71663132611898198782756685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47775421741265465855171123 71663132611898198782756685)
        ·
          refine ⟨26873674729461824543533757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71663132611898198782756685 26873674729461824543533757)
          ·
            refine ⟨10077628023548184203825159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26873674729461824543533757 10077628023548184203825159)
            ·
              refine ⟨15116442035322276305737739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10077628023548184203825159 15116442035322276305737739)
              ·
                refine ⟨22674663052983414458606609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15116442035322276305737739 22674663052983414458606609)
                ·
                  refine ⟨17005997289737560843954957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22674663052983414458606609 17005997289737560843954957)
                  ·
                    refine ⟨6377248983651585316483109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17005997289737560843954957 6377248983651585316483109)
                    ·
                      refine ⟨1195734184434672246840583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6377248983651585316483109 1195734184434672246840583)
                      ·
                        rfl

theorem cell23_2328684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_2328684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328684 prefixEnd_2328684 := by exact prefixLift 2328684
  have htrace : WordTrace (prefixWord ++ tailWord_2328684) baseStart_2328684 baseEnd_2328684 := by
    simpa [prefixWord, tailWord_2328684, baseEnd_2328684] using wordTrace_append hprefix tailTrace_2328684
  have hstable : (prefixWord ++ tailWord_2328684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328684).length < 2 ^ (prefixWord ++ tailWord_2328684).sum := by decide
  have hdescent : baseEnd_2328684 < baseStart_2328684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328704 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 3]
def baseStart_2328704 : Nat := 118140960795 + 2328704 * 2 ^ 59
def prefixEnd_2328704 : Nat := 4983230072969 + 3 ^ 40 * 2328704 * 2
def baseEnd_2328704 : Nat := 1195744454047762168590491

theorem tailTrace_2328704 : CollatzResearch.WordTrace tailWord_2328704 prefixEnd_2328704 1195744454047762168590491 := by
  unfold tailWord_2328704
  simp only [CollatzResearch.WordTrace]
  refine ⟨42467406277755296912460583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56623208370340395883280777 42467406277755296912460583)
  ·
    refine ⟨63701109416632945368690875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42467406277755296912460583 63701109416632945368690875)
    ·
      refine ⟨95551664124949418053036313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63701109416632945368690875 95551664124949418053036313)
      ·
        refine ⟨71663748093712063539777235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95551664124949418053036313 71663748093712063539777235)
        ·
          refine ⟨107495622140568095309665853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71663748093712063539777235 107495622140568095309665853)
          ·
            refine ⟨40310858302713035741124695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107495622140568095309665853 40310858302713035741124695)
            ·
              refine ⟨60466287454069553611687043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40310858302713035741124695 60466287454069553611687043)
              ·
                refine ⟨90699431181104330417530565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60466287454069553611687043 90699431181104330417530565)
                ·
                  refine ⟨17006143346457061953286981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90699431181104330417530565 17006143346457061953286981)
                  ·
                    refine ⟨3188651877460699116241309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17006143346457061953286981 3188651877460699116241309)
                    ·
                      refine ⟨1195744454047762168590491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3188651877460699116241309 1195744454047762168590491)
                      ·
                        rfl

theorem cell23_2328704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 3].length) (baseStart_2328704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328704 prefixEnd_2328704 := by exact prefixLift 2328704
  have htrace : WordTrace (prefixWord ++ tailWord_2328704) baseStart_2328704 baseEnd_2328704 := by
    simpa [prefixWord, tailWord_2328704, baseEnd_2328704] using wordTrace_append hprefix tailTrace_2328704
  have hstable : (prefixWord ++ tailWord_2328704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328704).length < 2 ^ (prefixWord ++ tailWord_2328704).sum := by decide
  have hdescent : baseEnd_2328704 < baseStart_2328704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328735 : List Nat := [1, 1, 2, 6, 1, 2, 1, 1, 4, 2, 2]
def baseStart_2328735 : Nat := 118140960795 + 2328735 * 2 ^ 59
def prefixEnd_2328735 : Nat := 4983230072969 + 3 ^ 40 * 2328735 * 2
def baseEnd_2328735 : Nat := 1195760371948051547302849

theorem tailTrace_2328735 : CollatzResearch.WordTrace tailWord_2328735 prefixEnd_2328735 1195760371948051547302849 := by
  unfold tailWord_2328735
  simp only [CollatzResearch.WordTrace]
  refine ⟨84935943218398286119299659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56623962145598857412866439 84935943218398286119299659)
  ·
    refine ⟨127403914827597429178949489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84935943218398286119299659 127403914827597429178949489)
    ·
      refine ⟨95552936120698071884212117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127403914827597429178949489 95552936120698071884212117)
      ·
        refine ⟨4479043880657722119572443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 95552936120698071884212117 4479043880657722119572443)
        ·
          refine ⟨6718565820986583179358665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4479043880657722119572443 6718565820986583179358665)
          ·
            refine ⟨5038924365739937384518999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6718565820986583179358665 5038924365739937384518999)
            ·
              refine ⟨7558386548609906076778499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5038924365739937384518999 7558386548609906076778499)
              ·
                refine ⟨11337579822914859115167749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7558386548609906076778499 11337579822914859115167749)
                ·
                  refine ⟨2125796216796536084093953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11337579822914859115167749 2125796216796536084093953)
                  ·
                    refine ⟨1594347162597402063070465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2125796216796536084093953 1594347162597402063070465)
                    ·
                      refine ⟨1195760371948051547302849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1594347162597402063070465 1195760371948051547302849)
                      ·
                        rfl

theorem cell23_2328735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_2328735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328735 prefixEnd_2328735 := by exact prefixLift 2328735
  have htrace : WordTrace (prefixWord ++ tailWord_2328735) baseStart_2328735 baseEnd_2328735 := by
    simpa [prefixWord, tailWord_2328735, baseEnd_2328735] using wordTrace_append hprefix tailTrace_2328735
  have hstable : (prefixWord ++ tailWord_2328735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328735).length < 2 ^ (prefixWord ++ tailWord_2328735).sum := by decide
  have hdescent : baseEnd_2328735 < baseStart_2328735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328741 : List Nat := [1, 3, 1, 2, 1, 3, 1, 6, 5]
def baseStart_2328741 : Nat := 118140960795 + 2328741 * 2 ^ 59
def prefixEnd_2328741 : Nat := 4983230072969 + 3 ^ 40 * 2328741 * 2
def baseEnd_2328741 : Nat := 132862605870219835980869

theorem tailTrace_2328741 : CollatzResearch.WordTrace tailWord_2328741 prefixEnd_2328741 132862605870219835980869 := by
  unfold tailWord_2328741
  simp only [CollatzResearch.WordTrace]
  refine ⟨84936162056376549144018077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56624108037584366096012051 84936162056376549144018077)
  ·
    refine ⟨31851060771141205929006779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84936162056376549144018077 31851060771141205929006779)
    ·
      refine ⟨47776591156711808893510169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31851060771141205929006779 47776591156711808893510169)
      ·
        refine ⟨35832443367533856670132627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47776591156711808893510169 35832443367533856670132627)
        ·
          refine ⟨53748665051300785005198941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35832443367533856670132627 53748665051300785005198941)
          ·
            refine ⟨20155749394237794376949603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53748665051300785005198941 20155749394237794376949603)
            ·
              refine ⟨30233624091356691565424405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20155749394237794376949603 30233624091356691565424405)
              ·
                refine ⟨1417201129282344917129269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30233624091356691565424405 1417201129282344917129269)
                ·
                  refine ⟨132862605870219835980869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1417201129282344917129269 132862605870219835980869)
                  ·
                    rfl

theorem cell23_2328741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 6, 5].length) (baseStart_2328741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328741 prefixEnd_2328741 := by exact prefixLift 2328741
  have htrace : WordTrace (prefixWord ++ tailWord_2328741) baseStart_2328741 baseEnd_2328741 := by
    simpa [prefixWord, tailWord_2328741, baseEnd_2328741] using wordTrace_append hprefix tailTrace_2328741
  have hstable : (prefixWord ++ tailWord_2328741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328741).length < 2 ^ (prefixWord ++ tailWord_2328741).sum := by decide
  have hdescent : baseEnd_2328741 < baseStart_2328741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328754 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 3, 7]
def baseStart_2328754 : Nat := 118140960795 + 2328754 * 2 ^ 59
def prefixEnd_2328754 : Nat := 4983230072969 + 3 ^ 40 * 2328754 * 2
def baseEnd_2328754 : Nat := 398590042693495657655087

theorem tailTrace_2328754 : CollatzResearch.WordTrace tailWord_2328754 prefixEnd_2328754 398590042693495657655087 := by
  unfold tailWord_2328754
  simp only [CollatzResearch.WordTrace]
  refine ⟨21234159051332363091060329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56624424136886301576160877 21234159051332363091060329)
  ·
    refine ⟨15925619288499272318295247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21234159051332363091060329 15925619288499272318295247)
    ·
      refine ⟨23888428932748908477442871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15925619288499272318295247 23888428932748908477442871)
      ·
        refine ⟨35832643399123362716164307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23888428932748908477442871 35832643399123362716164307)
        ·
          refine ⟨53748965098685044074246461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35832643399123362716164307 53748965098685044074246461)
          ·
            refine ⟨20155861912006891527842423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53748965098685044074246461 20155861912006891527842423)
            ·
              refine ⟨30233792868010337291763635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20155861912006891527842423 30233792868010337291763635)
              ·
                refine ⟨45350689302015505937645453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30233792868010337291763635 45350689302015505937645453)
                ·
                  refine ⟨17006508488255814726617045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45350689302015505937645453 17006508488255814726617045)
                  ·
                    refine ⟨398590042693495657655087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17006508488255814726617045 398590042693495657655087)
                    ·
                      rfl

theorem cell23_2328754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_2328754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328754 prefixEnd_2328754 := by exact prefixLift 2328754
  have htrace : WordTrace (prefixWord ++ tailWord_2328754) baseStart_2328754 baseEnd_2328754 := by
    simpa [prefixWord, tailWord_2328754, baseEnd_2328754] using wordTrace_append hprefix tailTrace_2328754
  have hstable : (prefixWord ++ tailWord_2328754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328754).length < 2 ^ (prefixWord ++ tailWord_2328754).sum := by decide
  have hdescent : baseEnd_2328754 < baseStart_2328754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328756 : List Nat := [2, 5, 3, 1, 1, 1, 2, 2, 1, 3, 2]
def baseStart_2328756 : Nat := 118140960795 + 2328756 * 2 ^ 59
def prefixEnd_2328756 : Nat := 4983230072969 + 3 ^ 40 * 2328756 * 2
def baseEnd_2328756 : Nat := 1195771155041795965140253

theorem tailTrace_2328756 : CollatzResearch.WordTrace tailWord_2328756 prefixEnd_2328756 1195771155041795965140253 := by
  unfold tailWord_2328756
  simp only [CollatzResearch.WordTrace]
  refine ⟨42468354575661103352907061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56624472767548137803876081 42468354575661103352907061)
  ·
    refine ⟨3981408241468228439335037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42468354575661103352907061 3981408241468228439335037)
    ·
      refine ⟨1493028090550585664750639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3981408241468228439335037 1493028090550585664750639)
      ·
        refine ⟨2239542135825878497125959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1493028090550585664750639 2239542135825878497125959)
        ·
          refine ⟨3359313203738817745688939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2239542135825878497125959 3359313203738817745688939)
          ·
            refine ⟨5038969805608226618533409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3359313203738817745688939 5038969805608226618533409)
            ·
              refine ⟨3779227354206169963900057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5038969805608226618533409 3779227354206169963900057)
              ·
                refine ⟨2834420515654627472925043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3779227354206169963900057 2834420515654627472925043)
                ·
                  refine ⟨4251630773481941209387565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2834420515654627472925043 4251630773481941209387565)
                  ·
                    refine ⟨1594361540055727953520337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4251630773481941209387565 1594361540055727953520337)
                    ·
                      refine ⟨1195771155041795965140253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1594361540055727953520337 1195771155041795965140253)
                      ·
                        rfl

theorem cell23_2328756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_2328756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328756 prefixEnd_2328756 := by exact prefixLift 2328756
  have htrace : WordTrace (prefixWord ++ tailWord_2328756) baseStart_2328756 baseEnd_2328756 := by
    simpa [prefixWord, tailWord_2328756, baseEnd_2328756] using wordTrace_append hprefix tailTrace_2328756
  have hstable : (prefixWord ++ tailWord_2328756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328756).length < 2 ^ (prefixWord ++ tailWord_2328756).sum := by decide
  have hdescent : baseEnd_2328756 < baseStart_2328756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328811 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 4, 2, 3]
def baseStart_2328811 : Nat := 118140960795 + 2328811 * 2 ^ 59
def prefixEnd_2328811 : Nat := 4983230072969 + 3 ^ 40 * 2328811 * 2
def baseEnd_2328811 : Nat := 1195799396477793249952499

theorem tailTrace_2328811 : CollatzResearch.WordTrace tailWord_2328811 prefixEnd_2328811 1195799396477793249952499 := by
  unfold tailWord_2328811
  simp only [CollatzResearch.WordTrace]
  refine ⟨84938715166122951099066287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56625810110748634066044191 84938715166122951099066287)
  ·
    refine ⟨127408072749184426648599431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84938715166122951099066287 127408072749184426648599431)
    ·
      refine ⟨191112109123776639972899147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127408072749184426648599431 191112109123776639972899147)
      ·
        refine ⟨286668163685664959959348721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191112109123776639972899147 286668163685664959959348721)
        ·
          refine ⟨215001122764248719969511541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286668163685664959959348721 215001122764248719969511541)
          ·
            refine ⟨20156355259148317497141707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 215001122764248719969511541 20156355259148317497141707)
            ·
              refine ⟨30234532888722476245712561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20156355259148317497141707 30234532888722476245712561)
              ·
                refine ⟨22675899666541857184284421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30234532888722476245712561 22675899666541857184284421)
                ·
                  refine ⟨4251731187476598222053329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22675899666541857184284421 4251731187476598222053329)
                  ·
                    refine ⟨3188798390607448666539997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4251731187476598222053329 3188798390607448666539997)
                    ·
                      refine ⟨1195799396477793249952499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3188798390607448666539997 1195799396477793249952499)
                      ·
                        rfl

theorem cell23_2328811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 2, 3].length) (baseStart_2328811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328811 prefixEnd_2328811 := by exact prefixLift 2328811
  have htrace : WordTrace (prefixWord ++ tailWord_2328811) baseStart_2328811 baseEnd_2328811 := by
    simpa [prefixWord, tailWord_2328811, baseEnd_2328811] using wordTrace_append hprefix tailTrace_2328811
  have hstable : (prefixWord ++ tailWord_2328811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328811).length < 2 ^ (prefixWord ++ tailWord_2328811).sum := by decide
  have hdescent : baseEnd_2328811 < baseStart_2328811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328828 : List Nat := [2, 2, 2, 1, 4, 1, 1, 3, 2, 2, 3]
def baseStart_2328828 : Nat := 118140960795 + 2328828 * 2 ^ 59
def prefixEnd_2328828 : Nat := 4983230072969 + 3 ^ 40 * 2328828 * 2
def baseEnd_2328828 : Nat := 1195808125648919683439921

theorem tailTrace_2328828 : CollatzResearch.WordTrace tailWord_2328828 prefixEnd_2328828 1195808125648919683439921 := by
  unfold tailWord_2328828
  simp only [CollatzResearch.WordTrace]
  refine ⟨42469667603530681501217569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56626223471374242001623425 42469667603530681501217569)
  ·
    refine ⟨31852250702648011125913177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42469667603530681501217569 31852250702648011125913177)
    ·
      refine ⟨23889188026986008344434883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31852250702648011125913177 23889188026986008344434883)
      ·
        refine ⟨35833782040479012516652325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23889188026986008344434883 35833782040479012516652325)
        ·
          refine ⟨6718834132589814846872311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35833782040479012516652325 6718834132589814846872311)
          ·
            refine ⟨10078251198884722270308467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6718834132589814846872311 10078251198884722270308467)
            ·
              refine ⟨15117376798327083405462701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10078251198884722270308467 15117376798327083405462701)
              ·
                refine ⟨5669016299372656277048513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15117376798327083405462701 5669016299372656277048513)
                ·
                  refine ⟨4251762224529492207786385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5669016299372656277048513 4251762224529492207786385)
                  ·
                    refine ⟨3188821668397119155839789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4251762224529492207786385 3188821668397119155839789)
                    ·
                      refine ⟨1195808125648919683439921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3188821668397119155839789 1195808125648919683439921)
                      ·
                        rfl

theorem cell23_2328828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_2328828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328828 prefixEnd_2328828 := by exact prefixLift 2328828
  have htrace : WordTrace (prefixWord ++ tailWord_2328828) baseStart_2328828 baseEnd_2328828 := by
    simpa [prefixWord, tailWord_2328828, baseEnd_2328828] using wordTrace_append hprefix tailTrace_2328828
  have hstable : (prefixWord ++ tailWord_2328828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328828).length < 2 ^ (prefixWord ++ tailWord_2328828).sum := by decide
  have hdescent : baseEnd_2328828 < baseStart_2328828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328892 : List Nat := [2, 2, 2, 2, 1, 2, 4, 3, 1, 1, 3]
def baseStart_2328892 : Nat := 118140960795 + 2328892 * 2 ^ 59
def prefixEnd_2328892 : Nat := 4983230072969 + 3 ^ 40 * 2328892 * 2
def baseEnd_2328892 : Nat := 1195840988410807433039627

theorem tailTrace_2328892 : CollatzResearch.WordTrace tailWord_2328892 prefixEnd_2328892 1195840988410807433039627 := by
  unfold tailWord_2328892
  simp only [CollatzResearch.WordTrace]
  refine ⟨42470834739414750966382465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56627779652553001288509953 42470834739414750966382465)
  ·
    refine ⟨31853126054561063224786849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42470834739414750966382465 31853126054561063224786849)
    ·
      refine ⟨23889844540920797418590137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31853126054561063224786849 23889844540920797418590137)
      ·
        refine ⟨17917383405690598063942603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23889844540920797418590137 17917383405690598063942603)
        ·
          refine ⟨26876075108535897095913905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17917383405690598063942603 26876075108535897095913905)
          ·
            refine ⟨20157056331401922821935429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26876075108535897095913905 20157056331401922821935429)
            ·
              refine ⟨3779448062137860529112893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20157056331401922821935429 3779448062137860529112893)
              ·
                refine ⟨1417293023301697698417335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3779448062137860529112893 1417293023301697698417335)
                ·
                  refine ⟨2125939534952546547626003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1417293023301697698417335 2125939534952546547626003)
                  ·
                    refine ⟨3188909302428819821439005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2125939534952546547626003 3188909302428819821439005)
                    ·
                      refine ⟨1195840988410807433039627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3188909302428819821439005 1195840988410807433039627)
                      ·
                        rfl

theorem cell23_2328892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_2328892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328892 prefixEnd_2328892 := by exact prefixLift 2328892
  have htrace : WordTrace (prefixWord ++ tailWord_2328892) baseStart_2328892 baseEnd_2328892 := by
    simpa [prefixWord, tailWord_2328892, baseEnd_2328892] using wordTrace_append hprefix tailTrace_2328892
  have hstable : (prefixWord ++ tailWord_2328892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328892).length < 2 ^ (prefixWord ++ tailWord_2328892).sum := by decide
  have hdescent : baseEnd_2328892 < baseStart_2328892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328908 : List Nat := [2, 2, 1, 3, 2, 1, 3, 1, 4, 4]
def baseStart_2328908 : Nat := 118140960795 + 2328908 * 2 ^ 59
def prefixEnd_2328908 : Nat := 4983230072969 + 3 ^ 40 * 2328908 * 2
def baseEnd_2328908 : Nat := 398616401367093123479851

theorem tailTrace_2328908 : CollatzResearch.WordTrace tailWord_2328908 prefixEnd_2328908 398616401367093123479851 := by
  unfold tailWord_2328908
  simp only [CollatzResearch.WordTrace]
  refine ⟨42471126523385768332673689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56628168697847691110231585 42471126523385768332673689)
  ·
    refine ⟨31853344892539326249505267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42471126523385768332673689 31853344892539326249505267)
    ·
      refine ⟨47780017338808989374257901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31853344892539326249505267 47780017338808989374257901)
      ·
        refine ⟨17917506502053371015346713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47780017338808989374257901 17917506502053371015346713)
        ·
          refine ⟨13438129876540028261510035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17917506502053371015346713 13438129876540028261510035)
          ·
            refine ⟨20157194814810042392265053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13438129876540028261510035 20157194814810042392265053)
            ·
              refine ⟨7558948055553765897099395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20157194814810042392265053 7558948055553765897099395)
              ·
                refine ⟨11338422083330648845649093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7558948055553765897099395 11338422083330648845649093)
                ·
                  refine ⟨2125954140624496658559205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11338422083330648845649093 2125954140624496658559205)
                  ·
                    refine ⟨398616401367093123479851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2125954140624496658559205 398616401367093123479851)
                    ·
                      rfl

theorem cell23_2328908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 4, 4].length) (baseStart_2328908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328908 prefixEnd_2328908 := by exact prefixLift 2328908
  have htrace : WordTrace (prefixWord ++ tailWord_2328908) baseStart_2328908 baseEnd_2328908 := by
    simpa [prefixWord, tailWord_2328908, baseEnd_2328908] using wordTrace_append hprefix tailTrace_2328908
  have hstable : (prefixWord ++ tailWord_2328908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328908).length < 2 ^ (prefixWord ++ tailWord_2328908).sum := by decide
  have hdescent : baseEnd_2328908 < baseStart_2328908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328928 : List Nat := [2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 6]
def baseStart_2328928 : Nat := 118140960795 + 2328928 * 2 ^ 59
def prefixEnd_2328928 : Nat := 4983230072969 + 3 ^ 40 * 2328928 * 2
def baseEnd_2328928 : Nat := 1195859473714369292189461

theorem tailTrace_2328928 : CollatzResearch.WordTrace tailWord_2328928 prefixEnd_2328928 1195859473714369292189461 := by
  unfold tailWord_2328928
  simp only [CollatzResearch.WordTrace]
  refine ⟨42471491253349540040537719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56628655004466053387383625 42471491253349540040537719)
  ·
    refine ⟨63707236880024310060806579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42471491253349540040537719 63707236880024310060806579)
    ·
      refine ⟨95560855320036465091209869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63707236880024310060806579 95560855320036465091209869)
      ·
        refine ⟨35835320745013674409203701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95560855320036465091209869 35835320745013674409203701)
        ·
          refine ⟨3359561319845031975862847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35835320745013674409203701 3359561319845031975862847)
          ·
            refine ⟨5039341979767547963794271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3359561319845031975862847 5039341979767547963794271)
            ·
              refine ⟨7559012969651321945691407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5039341979767547963794271 7559012969651321945691407)
              ·
                refine ⟨11338519454476982918537111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7559012969651321945691407 11338519454476982918537111)
                ·
                  refine ⟨17007779181715474377805667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11338519454476982918537111 17007779181715474377805667)
                  ·
                    refine ⟨25511668772573211566708501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17007779181715474377805667 25511668772573211566708501)
                    ·
                      refine ⟨1195859473714369292189461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25511668772573211566708501 1195859473714369292189461)
                      ·
                        rfl

theorem cell23_2328928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_2328928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328928 prefixEnd_2328928 := by exact prefixLift 2328928
  have htrace : WordTrace (prefixWord ++ tailWord_2328928) baseStart_2328928 baseEnd_2328928 := by
    simpa [prefixWord, tailWord_2328928, baseEnd_2328928] using wordTrace_append hprefix tailTrace_2328928
  have hstable : (prefixWord ++ tailWord_2328928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328928).length < 2 ^ (prefixWord ++ tailWord_2328928).sum := by decide
  have hdescent : baseEnd_2328928 < baseStart_2328928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328935 : List Nat := [1, 1, 5, 1, 3, 1, 1, 4, 1, 2, 3]
def baseStart_2328935 : Nat := 118140960795 + 2328935 * 2 ^ 59
def prefixEnd_2328935 : Nat := 4983230072969 + 3 ^ 40 * 2328935 * 2
def baseEnd_2328935 : Nat := 1195863068078950764801929

theorem tailTrace_2328935 : CollatzResearch.WordTrace tailWord_2328935 prefixEnd_2328935 1195863068078950764801929 := by
  unfold tailWord_2328935
  simp only [CollatzResearch.WordTrace]
  refine ⟨84943237817673720276580259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56628825211782480184386839 84943237817673720276580259)
  ·
    refine ⟨127414856726510580414870389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84943237817673720276580259 127414856726510580414870389)
    ·
      refine ⟨11945142818110366913894099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 127414856726510580414870389 11945142818110366913894099)
      ·
        refine ⟨17917714227165550370841149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11945142818110366913894099 17917714227165550370841149)
        ·
          refine ⟨6719142835187081389065431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17917714227165550370841149 6719142835187081389065431)
          ·
            refine ⟨10078714252780622083598147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6719142835187081389065431 10078714252780622083598147)
            ·
              refine ⟨15118071379170933125397221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10078714252780622083598147 15118071379170933125397221)
              ·
                refine ⟨2834638383594549961011979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15118071379170933125397221 2834638383594549961011979)
                ·
                  refine ⟨4251957575391824941517969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2834638383594549961011979 4251957575391824941517969)
                  ·
                    refine ⟨3188968181543868706138477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4251957575391824941517969 3188968181543868706138477)
                    ·
                      refine ⟨1195863068078950764801929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3188968181543868706138477 1195863068078950764801929)
                      ·
                        rfl

theorem cell23_2328935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_2328935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328935 prefixEnd_2328935 := by exact prefixLift 2328935
  have htrace : WordTrace (prefixWord ++ tailWord_2328935) baseStart_2328935 baseEnd_2328935 := by
    simpa [prefixWord, tailWord_2328935, baseEnd_2328935] using wordTrace_append hprefix tailTrace_2328935
  have hstable : (prefixWord ++ tailWord_2328935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328935).length < 2 ^ (prefixWord ++ tailWord_2328935).sum := by decide
  have hdescent : baseEnd_2328935 < baseStart_2328935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328938 : List Nat := [3, 1, 3, 3, 1, 2, 1, 9]
def baseStart_2328938 : Nat := 118140960795 + 2328938 * 2 ^ 59
def prefixEnd_2328938 : Nat := 4983230072969 + 3 ^ 40 * 2328938 * 2
def baseEnd_2328938 : Nat := 44291281797070898261645

theorem tailTrace_2328938 : CollatzResearch.WordTrace tailWord_2328938 prefixEnd_2328938 44291281797070898261645 := by
  unfold tailWord_2328938
  simp only [CollatzResearch.WordTrace]
  refine ⟨21235836809165712947234867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56628898157775234525959645 21235836809165712947234867)
  ·
    refine ⟨31853755213748569420852301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21235836809165712947234867 31853755213748569420852301)
    ·
      refine ⟨11945158205155713532819613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31853755213748569420852301 11945158205155713532819613)
      ·
        refine ⟨4479434326933392574807355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11945158205155713532819613 4479434326933392574807355)
        ·
          refine ⟨6719151490400088862211033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4479434326933392574807355 6719151490400088862211033)
          ·
            refine ⟨5039363617800066646658275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6719151490400088862211033 5039363617800066646658275)
            ·
              refine ⟨7559045426700099969987413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5039363617800066646658275 7559045426700099969987413)
              ·
                refine ⟨44291281797070898261645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7559045426700099969987413 44291281797070898261645)
                ·
                  rfl

theorem cell23_2328938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 9].length) (baseStart_2328938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328938 prefixEnd_2328938 := by exact prefixLift 2328938
  have htrace : WordTrace (prefixWord ++ tailWord_2328938) baseStart_2328938 baseEnd_2328938 := by
    simpa [prefixWord, tailWord_2328938, baseEnd_2328938] using wordTrace_append hprefix tailTrace_2328938
  have hstable : (prefixWord ++ tailWord_2328938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328938).length < 2 ^ (prefixWord ++ tailWord_2328938).sum := by decide
  have hdescent : baseEnd_2328938 < baseStart_2328938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328965 : List Nat := [1, 3, 1, 1, 3, 1, 1, 6, 2, 1, 3]
def baseStart_2328965 : Nat := 118140960795 + 2328965 * 2 ^ 59
def prefixEnd_2328965 : Nat := 4983230072969 + 3 ^ 40 * 2328965 * 2
def baseEnd_2328965 : Nat := 1195878472498585647426791

theorem tailTrace_2328965 : CollatzResearch.WordTrace tailWord_2328965 prefixEnd_2328965 1195878472498585647426791 := by
  unfold tailWord_2328965
  simp only [CollatzResearch.WordTrace]
  refine ⟨84944332007565035400172349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56629554671710023600114899 84944332007565035400172349)
  ·
    refine ⟨31854124502836888275064631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84944332007565035400172349 31854124502836888275064631)
    ·
      refine ⟨47781186754255332412596947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31854124502836888275064631 47781186754255332412596947)
      ·
        refine ⟨71671780131382998618895421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47781186754255332412596947 71671780131382998618895421)
        ·
          refine ⟨26876917549268624482085783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71671780131382998618895421 26876917549268624482085783)
          ·
            refine ⟨40315376323902936723128675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26876917549268624482085783 40315376323902936723128675)
            ·
              refine ⟨60473064485854405084693013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40315376323902936723128675 60473064485854405084693013)
              ·
                refine ⟨2834674897774425238344985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60473064485854405084693013 2834674897774425238344985)
                ·
                  refine ⟨2126006173330818928758739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2834674897774425238344985 2126006173330818928758739)
                  ·
                    refine ⟨3189009259996228393138109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2126006173330818928758739 3189009259996228393138109)
                    ·
                      refine ⟨1195878472498585647426791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3189009259996228393138109 1195878472498585647426791)
                      ·
                        rfl

theorem cell23_2328965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 2, 1, 3].length) (baseStart_2328965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328965 prefixEnd_2328965 := by exact prefixLift 2328965
  have htrace : WordTrace (prefixWord ++ tailWord_2328965) baseStart_2328965 baseEnd_2328965 := by
    simpa [prefixWord, tailWord_2328965, baseEnd_2328965] using wordTrace_append hprefix tailTrace_2328965
  have hstable : (prefixWord ++ tailWord_2328965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328965).length < 2 ^ (prefixWord ++ tailWord_2328965).sum := by decide
  have hdescent : baseEnd_2328965 < baseStart_2328965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328981 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 1, 8]
def baseStart_2328981 : Nat := 118140960795 + 2328981 * 2 ^ 59
def prefixEnd_2328981 : Nat := 4983230072969 + 3 ^ 40 * 2328981 * 2
def baseEnd_2328981 : Nat := 398628896063019194942239

theorem tailTrace_2328981 : CollatzResearch.WordTrace tailWord_2328981 prefixEnd_2328981 398628896063019194942239 := by
  unfold tailWord_2328981
  simp only [CollatzResearch.WordTrace]
  refine ⟨84944915575507070132754797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56629943717004713421836531 84944915575507070132754797)
  ·
    refine ⟨31854343340815151299783049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84944915575507070132754797 31854343340815151299783049)
    ·
      refine ⟨23890757505611363474837287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31854343340815151299783049 23890757505611363474837287)
      ·
        refine ⟨35836136258417045212255931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23890757505611363474837287 35836136258417045212255931)
        ·
          refine ⟨53754204387625567818383897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35836136258417045212255931 53754204387625567818383897)
          ·
            refine ⟨40315653290719175863787923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53754204387625567818383897 40315653290719175863787923)
            ·
              refine ⟨60473479936078763795681885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40315653290719175863787923 60473479936078763795681885)
              ·
                refine ⟨22677554976029536423380707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60473479936078763795681885 22677554976029536423380707)
                ·
                  refine ⟨34016332464044304635071061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22677554976029536423380707 34016332464044304635071061)
                  ·
                    refine ⟨398628896063019194942239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34016332464044304635071061 398628896063019194942239)
                    ·
                      rfl

theorem cell23_2328981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_2328981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328981 prefixEnd_2328981 := by exact prefixLift 2328981
  have htrace : WordTrace (prefixWord ++ tailWord_2328981) baseStart_2328981 baseEnd_2328981 := by
    simpa [prefixWord, tailWord_2328981, baseEnd_2328981] using wordTrace_append hprefix tailTrace_2328981
  have hstable : (prefixWord ++ tailWord_2328981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328981).length < 2 ^ (prefixWord ++ tailWord_2328981).sum := by decide
  have hdescent : baseEnd_2328981 < baseStart_2328981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2328992 : List Nat := [2, 1, 1, 4, 1, 3, 3, 2, 1, 3, 2]
def baseStart_2328992 : Nat := 118140960795 + 2328992 * 2 ^ 59
def prefixEnd_2328992 : Nat := 4983230072969 + 3 ^ 40 * 2328992 * 2
def baseEnd_2328992 : Nat := 1195892336476257041789167

theorem tailTrace_2328992 : CollatzResearch.WordTrace tailWord_2328992 prefixEnd_2328992 1195892336476257041789167 := by
  unfold tailWord_2328992
  simp only [CollatzResearch.WordTrace]
  refine ⟨42472658389233609505702615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56630211185644812674270153 42472658389233609505702615)
  ·
    refine ⟨63708987583850414258553923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42472658389233609505702615 63708987583850414258553923)
    ·
      refine ⟨95563481375775621387830885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63708987583850414258553923 95563481375775621387830885)
      ·
        refine ⟨17918152757957929010218291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95563481375775621387830885 17918152757957929010218291)
        ·
          refine ⟨26877229136936893515327437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17918152757957929010218291 26877229136936893515327437)
          ·
            refine ⟨10078960926351335068247789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26877229136936893515327437 10078960926351335068247789)
            ·
              refine ⟨3779610347381750650592921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10078960926351335068247789 3779610347381750650592921)
              ·
                refine ⟨2834707760536312987944691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3779610347381750650592921 2834707760536312987944691)
                ·
                  refine ⟨4252061640804469481917037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2834707760536312987944691 4252061640804469481917037)
                  ·
                    refine ⟨1594523115301676055718889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4252061640804469481917037 1594523115301676055718889)
                    ·
                      refine ⟨1195892336476257041789167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1594523115301676055718889 1195892336476257041789167)
                      ·
                        rfl

theorem cell23_2328992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_2328992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2328992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2328992 prefixEnd_2328992 := by exact prefixLift 2328992
  have htrace : WordTrace (prefixWord ++ tailWord_2328992) baseStart_2328992 baseEnd_2328992 := by
    simpa [prefixWord, tailWord_2328992, baseEnd_2328992] using wordTrace_append hprefix tailTrace_2328992
  have hstable : (prefixWord ++ tailWord_2328992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2328992).length < 2 ^ (prefixWord ++ tailWord_2328992).sum := by decide
  have hdescent : baseEnd_2328992 < baseStart_2328992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2328992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329009 : List Nat := [1, 2, 2, 4, 1, 3, 3, 1, 1, 3, 2]
def baseStart_2329009 : Nat := 118140960795 + 2329009 * 2 ^ 59
def prefixEnd_2329009 : Nat := 4983230072969 + 3 ^ 40 * 2329009 * 2
def baseEnd_2329009 : Nat := 1195901065647383475276589

theorem tailTrace_2329009 : CollatzResearch.WordTrace tailWord_2329009 prefixEnd_2329009 1195901065647383475276589 := by
  unfold tailWord_2329009
  simp only [CollatzResearch.WordTrace]
  refine ⟨84945936819405630914774081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56630624546270420609849387 84945936819405630914774081)
  ·
    refine ⟨63709452614554223186080561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84945936819405630914774081 63709452614554223186080561)
    ·
      refine ⟨47782089460915667389560421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63709452614554223186080561 47782089460915667389560421)
      ·
        refine ⟨8959141773921687635542579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47782089460915667389560421 8959141773921687635542579)
        ·
          refine ⟨13438712660882531453313869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8959141773921687635542579 13438712660882531453313869)
          ·
            refine ⟨5039517247830949294992701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13438712660882531453313869 5039517247830949294992701)
            ·
              refine ⟨1889818967936605985622263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5039517247830949294992701 1889818967936605985622263)
              ·
                refine ⟨2834728451904908978433395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1889818967936605985622263 2834728451904908978433395)
                ·
                  refine ⟨4252092677857363467650093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2834728451904908978433395 4252092677857363467650093)
                  ·
                    refine ⟨1594534754196511300368785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4252092677857363467650093 1594534754196511300368785)
                    ·
                      refine ⟨1195901065647383475276589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1594534754196511300368785 1195901065647383475276589)
                      ·
                        rfl

theorem cell23_2329009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_2329009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329009 prefixEnd_2329009 := by exact prefixLift 2329009
  have htrace : WordTrace (prefixWord ++ tailWord_2329009) baseStart_2329009 baseEnd_2329009 := by
    simpa [prefixWord, tailWord_2329009, baseEnd_2329009] using wordTrace_append hprefix tailTrace_2329009
  have hstable : (prefixWord ++ tailWord_2329009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329009).length < 2 ^ (prefixWord ++ tailWord_2329009).sum := by decide
  have hdescent : baseEnd_2329009 < baseStart_2329009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329022 : List Nat := [4, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2]
def baseStart_2329022 : Nat := 118140960795 + 2329022 * 2 ^ 59
def prefixEnd_2329022 : Nat := 4983230072969 + 3 ^ 40 * 2329022 * 2
def baseEnd_2329022 : Nat := 1195907740895891924414029

theorem tailTrace_2329022 : CollatzResearch.WordTrace tailWord_2329022 prefixEnd_2329022 1195907740895891924414029 := by
  unfold tailWord_2329022
  simp only [CollatzResearch.WordTrace]
  refine ⟨10618301371044816766874665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56630940645572356089998213 10618301371044816766874665)
  ·
    refine ⟨7963726028283612575155999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10618301371044816766874665 7963726028283612575155999)
    ·
      refine ⟨11945589042425418862733999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7963726028283612575155999 11945589042425418862733999)
      ·
        refine ⟨17918383563638128294100999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11945589042425418862733999 17918383563638128294100999)
        ·
          refine ⟨26877575345457192441151499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17918383563638128294100999 26877575345457192441151499)
          ·
            refine ⟨40316363018185788661727249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26877575345457192441151499 40316363018185788661727249)
            ·
              refine ⟨30237272263639341496295437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40316363018185788661727249 30237272263639341496295437)
              ·
                refine ⟨11338977098864753061110789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30237272263639341496295437 11338977098864753061110789)
                ·
                  refine ⟨2126058206037141198958273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11338977098864753061110789 2126058206037141198958273)
                  ·
                    refine ⟨1594543654527855899218705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2126058206037141198958273 1594543654527855899218705)
                    ·
                      refine ⟨1195907740895891924414029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1594543654527855899218705 1195907740895891924414029)
                      ·
                        rfl

theorem cell23_2329022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_2329022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329022 prefixEnd_2329022 := by exact prefixLift 2329022
  have htrace : WordTrace (prefixWord ++ tailWord_2329022) baseStart_2329022 baseEnd_2329022 := by
    simpa [prefixWord, tailWord_2329022, baseEnd_2329022] using wordTrace_append hprefix tailTrace_2329022
  have hstable : (prefixWord ++ tailWord_2329022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329022).length < 2 ^ (prefixWord ++ tailWord_2329022).sum := by decide
  have hdescent : baseEnd_2329022 < baseStart_2329022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329051 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 7]
def baseStart_2329051 : Nat := 118140960795 + 2329051 * 2 ^ 59
def prefixEnd_2329051 : Nat := 4983230072969 + 3 ^ 40 * 2329051 * 2
def baseEnd_2329051 : Nat := 1195922631834872310951395

theorem tailTrace_2329051 : CollatzResearch.WordTrace tailWord_2329051 prefixEnd_2329051 1195922631834872310951395 := by
  unfold tailWord_2329051
  simp only [CollatzResearch.WordTrace]
  refine ⟨84947468685253472087803007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56631645790168981391868671 84947468685253472087803007)
  ·
    refine ⟨127421203027880208131704511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84947468685253472087803007 127421203027880208131704511)
    ·
      refine ⟨191131804541820312197556767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127421203027880208131704511 191131804541820312197556767)
      ·
        refine ⟨286697706812730468296335151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191131804541820312197556767 286697706812730468296335151)
        ·
          refine ⟨430046560219095702444502727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286697706812730468296335151 430046560219095702444502727)
          ·
            refine ⟨645069840328643553666754091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 430046560219095702444502727 645069840328643553666754091)
            ·
              refine ⟨967604760492965330500131137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 645069840328643553666754091 967604760492965330500131137)
              ·
                refine ⟨725703570369723997875098353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 967604760492965330500131137 725703570369723997875098353)
                ·
                  refine ⟨544277677777292998406323765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 725703570369723997875098353 544277677777292998406323765)
                  ·
                    refine ⟨51026032291621218600592853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 544277677777292998406323765 51026032291621218600592853)
                    ·
                      refine ⟨1195922631834872310951395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 51026032291621218600592853 1195922631834872310951395)
                      ·
                        rfl

theorem cell23_2329051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 7].length) (baseStart_2329051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329051 prefixEnd_2329051 := by exact prefixLift 2329051
  have htrace : WordTrace (prefixWord ++ tailWord_2329051) baseStart_2329051 baseEnd_2329051 := by
    simpa [prefixWord, tailWord_2329051, baseEnd_2329051] using wordTrace_append hprefix tailTrace_2329051
  have hstable : (prefixWord ++ tailWord_2329051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329051).length < 2 ^ (prefixWord ++ tailWord_2329051).sum := by decide
  have hdescent : baseEnd_2329051 < baseStart_2329051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329138 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8]
def baseStart_2329138 : Nat := 118140960795 + 2329138 * 2 ^ 59
def prefixEnd_2329138 : Nat := 4983230072969 + 3 ^ 40 * 2329138 * 2
def baseEnd_2329138 : Nat := 1195967304651813470563495

theorem tailTrace_2329138 : CollatzResearch.WordTrace tailWord_2329138 prefixEnd_2329138 1195967304651813470563495 := by
  unfold tailWord_2329138
  simp only [CollatzResearch.WordTrace]
  refine ⟨21237660458984571486555017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56633761223958857297480045 21237660458984571486555017)
  ·
    refine ⟨15928245344238428614916263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21237660458984571486555017 15928245344238428614916263)
    ·
      refine ⟨23892368016357642922374395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15928245344238428614916263 23892368016357642922374395)
      ·
        refine ⟨35838552024536464383561593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23892368016357642922374395 35838552024536464383561593)
        ·
          refine ⟨26878914018402348287671195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35838552024536464383561593 26878914018402348287671195)
          ·
            refine ⟨40318371027603522431506793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26878914018402348287671195 40318371027603522431506793)
            ·
              refine ⟨30238778270702641823630095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40318371027603522431506793 30238778270702641823630095)
              ·
                refine ⟨45358167406053962735445143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30238778270702641823630095 45358167406053962735445143)
                ·
                  refine ⟨68037251109080944103167715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45358167406053962735445143 68037251109080944103167715)
                  ·
                    refine ⟨102055876663621416154751573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68037251109080944103167715 102055876663621416154751573)
                    ·
                      refine ⟨1195967304651813470563495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 102055876663621416154751573 1195967304651813470563495)
                      ·
                        rfl

theorem cell23_2329138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_2329138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329138 prefixEnd_2329138 := by exact prefixLift 2329138
  have htrace : WordTrace (prefixWord ++ tailWord_2329138) baseStart_2329138 baseEnd_2329138 := by
    simpa [prefixWord, tailWord_2329138, baseEnd_2329138] using wordTrace_append hprefix tailTrace_2329138
  have hstable : (prefixWord ++ tailWord_2329138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329138).length < 2 ^ (prefixWord ++ tailWord_2329138).sum := by decide
  have hdescent : baseEnd_2329138 < baseStart_2329138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329139 : List Nat := [1, 1, 1, 2, 4, 2, 5, 2, 1, 4]
def baseStart_2329139 : Nat := 118140960795 + 2329139 * 2 ^ 59
def prefixEnd_2329139 : Nat := 4983230072969 + 3 ^ 40 * 2329139 * 2
def baseEnd_2329139 : Nat := 398655939377489322216997

theorem tailTrace_2329139 : CollatzResearch.WordTrace tailWord_2329139 prefixEnd_2329139 398655939377489322216997 := by
  unfold tailWord_2329139
  simp only [CollatzResearch.WordTrace]
  refine ⟨84950678308934663117006471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56633785539289775411337647 84950678308934663117006471)
  ·
    refine ⟨127426017463401994675509707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84950678308934663117006471 127426017463401994675509707)
    ·
      refine ⟨191139026195102992013264561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127426017463401994675509707 191139026195102992013264561)
      ·
        refine ⟨143354269646327244009948421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191139026195102992013264561 143354269646327244009948421)
        ·
          refine ⟨26878925558686358251865329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143354269646327244009948421 26878925558686358251865329)
          ·
            refine ⟨20159194169014768688898997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26878925558686358251865329 20159194169014768688898997)
            ·
              refine ⟨1889924453345134564584281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20159194169014768688898997 1889924453345134564584281)
              ·
                refine ⟨1417443340008850923438211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1889924453345134564584281 1417443340008850923438211)
                ·
                  refine ⟨2126165010013276385157317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1417443340008850923438211 2126165010013276385157317)
                  ·
                    refine ⟨398655939377489322216997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2126165010013276385157317 398655939377489322216997)
                    ·
                      rfl

theorem cell23_2329139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 2, 1, 4].length) (baseStart_2329139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329139 prefixEnd_2329139 := by exact prefixLift 2329139
  have htrace : WordTrace (prefixWord ++ tailWord_2329139) baseStart_2329139 baseEnd_2329139 := by
    simpa [prefixWord, tailWord_2329139, baseEnd_2329139] using wordTrace_append hprefix tailTrace_2329139
  have hstable : (prefixWord ++ tailWord_2329139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329139).length < 2 ^ (prefixWord ++ tailWord_2329139).sum := by decide
  have hdescent : baseEnd_2329139 < baseStart_2329139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329155 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 3, 5, 2]
def baseStart_2329155 : Nat := 118140960795 + 2329155 * 2 ^ 59
def prefixEnd_2329155 : Nat := 4983230072969 + 3 ^ 40 * 2329155 * 2
def baseEnd_2329155 : Nat := 1195976033822939904050917

theorem tailTrace_2329155 : CollatzResearch.WordTrace tailWord_2329155 prefixEnd_2329155 1195976033822939904050917 := by
  unfold tailWord_2329155
  simp only [CollatzResearch.WordTrace]
  refine ⟨84951261876876697849588919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56634174584584465233059279 84951261876876697849588919)
  ·
    refine ⟨127426892815315046774383379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84951261876876697849588919 127426892815315046774383379)
    ·
      refine ⟨191140339222972570161575069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127426892815315046774383379 191140339222972570161575069)
      ·
        refine ⟨71677627208614713810590651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191140339222972570161575069 71677627208614713810590651)
        ·
          refine ⟨107516440812922070715885977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71677627208614713810590651 107516440812922070715885977)
          ·
            refine ⟨80637330609691553036914483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107516440812922070715885977 80637330609691553036914483)
            ·
              refine ⟨120955995914537329555371725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80637330609691553036914483 120955995914537329555371725)
              ·
                refine ⟨45358498467951498583264397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120955995914537329555371725 45358498467951498583264397)
                ·
                  refine ⟨17009436925481811968724149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45358498467951498583264397 17009436925481811968724149)
                  ·
                    refine ⟨1594634711763919872067889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17009436925481811968724149 1594634711763919872067889)
                    ·
                      refine ⟨1195976033822939904050917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1594634711763919872067889 1195976033822939904050917)
                      ·
                        rfl

theorem cell23_2329155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 5, 2].length) (baseStart_2329155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329155 prefixEnd_2329155 := by exact prefixLift 2329155
  have htrace : WordTrace (prefixWord ++ tailWord_2329155) baseStart_2329155 baseEnd_2329155 := by
    simpa [prefixWord, tailWord_2329155, baseEnd_2329155] using wordTrace_append hprefix tailTrace_2329155
  have hstable : (prefixWord ++ tailWord_2329155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329155).length < 2 ^ (prefixWord ++ tailWord_2329155).sum := by decide
  have hdescent : baseEnd_2329155 < baseStart_2329155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329196 : List Nat := [2, 2, 1, 1, 3, 1, 6, 2, 1, 1, 3]
def baseStart_2329196 : Nat := 118140960795 + 2329196 * 2 ^ 59
def prefixEnd_2329196 : Nat := 4983230072969 + 3 ^ 40 * 2329196 * 2
def baseEnd_2329196 : Nat := 1195997086529774243638229

theorem tailTrace_2329196 : CollatzResearch.WordTrace tailWord_2329196 prefixEnd_2329196 1195997086529774243638229 := by
  unfold tailWord_2329196
  simp only [CollatzResearch.WordTrace]
  refine ⟨42476378634864080925915721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56635171513152107901220961 42476378634864080925915721)
  ·
    refine ⟨31857283976148060694436791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42476378634864080925915721 31857283976148060694436791)
    ·
      refine ⟨47785925964222091041655187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31857283976148060694436791 47785925964222091041655187)
      ·
        refine ⟨71678888946333136562482781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47785925964222091041655187 71678888946333136562482781)
        ·
          refine ⟨26879583354874926210931043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71678888946333136562482781 26879583354874926210931043)
          ·
            refine ⟨40319375032312389316396565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26879583354874926210931043 40319375032312389316396565)
            ·
              refine ⟨1889970704639643249206089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40319375032312389316396565 1889970704639643249206089)
              ·
                refine ⟨1417478028479732436904567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1889970704639643249206089 1417478028479732436904567)
                ·
                  refine ⟨2126217042719598655356851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1417478028479732436904567 2126217042719598655356851)
                  ·
                    refine ⟨3189325564079397983035277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2126217042719598655356851 3189325564079397983035277)
                    ·
                      refine ⟨1195997086529774243638229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3189325564079397983035277 1195997086529774243638229)
                      ·
                        rfl

theorem cell23_2329196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 2, 1, 1, 3].length) (baseStart_2329196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329196 prefixEnd_2329196 := by exact prefixLift 2329196
  have htrace : WordTrace (prefixWord ++ tailWord_2329196) baseStart_2329196 baseEnd_2329196 := by
    simpa [prefixWord, tailWord_2329196, baseEnd_2329196] using wordTrace_append hprefix tailTrace_2329196
  have hstable : (prefixWord ++ tailWord_2329196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329196).length < 2 ^ (prefixWord ++ tailWord_2329196).sum := by decide
  have hdescent : baseEnd_2329196 < baseStart_2329196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329212 : List Nat := [2, 2, 2, 1, 1, 2, 4, 3, 2, 4]
def baseStart_2329212 : Nat := 118140960795 + 2329212 * 2 ^ 59
def prefixEnd_2329212 : Nat := 4983230072969 + 3 ^ 40 * 2329212 * 2
def baseEnd_2329212 : Nat := 398668434073415393679385

theorem tailTrace_2329212 : CollatzResearch.WordTrace tailWord_2329212 prefixEnd_2329212 398668434073415393679385 := by
  unfold tailWord_2329212
  simp only [CollatzResearch.WordTrace]
  refine ⟨42476670418835098292206945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56635560558446797722942593 42476670418835098292206945)
  ·
    refine ⟨31857502814126323719155209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42476670418835098292206945 31857502814126323719155209)
    ·
      refine ⟨23893127110594742789366407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31857502814126323719155209 23893127110594742789366407)
      ·
        refine ⟨35839690665892114184049611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23893127110594742789366407 35839690665892114184049611)
        ·
          refine ⟨53759535998838171276074417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35839690665892114184049611 53759535998838171276074417)
          ·
            refine ⟨40319651999128628457055813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53759535998838171276074417 40319651999128628457055813)
            ·
              refine ⟨7559934749836617835697965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40319651999128628457055813 7559934749836617835697965)
              ·
                refine ⟨2834975531188731688386737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7559934749836617835697965 2834975531188731688386737)
                ·
                  refine ⟨2126231648391548766290053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2834975531188731688386737 2126231648391548766290053)
                  ·
                    refine ⟨398668434073415393679385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2126231648391548766290053 398668434073415393679385)
                    ·
                      rfl

theorem cell23_2329212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_2329212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329212 prefixEnd_2329212 := by exact prefixLift 2329212
  have htrace : WordTrace (prefixWord ++ tailWord_2329212) baseStart_2329212 baseEnd_2329212 := by
    simpa [prefixWord, tailWord_2329212, baseEnd_2329212] using wordTrace_append hprefix tailTrace_2329212
  have hstable : (prefixWord ++ tailWord_2329212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329212).length < 2 ^ (prefixWord ++ tailWord_2329212).sum := by decide
  have hdescent : baseEnd_2329212 < baseStart_2329212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
