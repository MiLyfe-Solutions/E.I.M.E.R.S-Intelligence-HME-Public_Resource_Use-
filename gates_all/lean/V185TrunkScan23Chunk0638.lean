import V185TrunkScan23Chunk0637

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3773341 : List Nat := [1, 4, 2, 1, 2, 1, 4, 3, 1, 1, 3]
def baseStart_3773341 : Nat := 118140960795 + 3773341 * 2 ^ 59
def prefixEnd_3773341 : Nat := 4983230072969 + 3 ^ 40 * 3773341 * 2
def baseEnd_3773341 : Nat := 1937537606317026519684227

theorem tailTrace_3773341 : CollatzResearch.WordTrace tailWord_3773341 prefixEnd_3773341 1937537606317026519684227 := by
  unfold tailWord_3773341
  simp only [CollatzResearch.WordTrace]
  refine ⟨137625052622837467181791877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91750035081891644787861251 137625052622837467181791877)
  ·
    refine ⟨25804697366782025096585977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137625052622837467181791877 25804697366782025096585977)
    ·
      refine ⟨19353523025086518822439483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25804697366782025096585977 19353523025086518822439483)
      ·
        refine ⟨29030284537629778233659225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19353523025086518822439483 29030284537629778233659225)
        ·
          refine ⟨21772713403222333675244419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29030284537629778233659225 21772713403222333675244419)
          ·
            refine ⟨32659070104833500512866629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21772713403222333675244419 32659070104833500512866629)
            ·
              refine ⟨6123575644656281346162493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32659070104833500512866629 6123575644656281346162493)
              ·
                refine ⟨2296340866746105504810935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6123575644656281346162493 2296340866746105504810935)
                ·
                  refine ⟨3444511300119158257216403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2296340866746105504810935 3444511300119158257216403)
                  ·
                    refine ⟨5166766950178737385824605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3444511300119158257216403 5166766950178737385824605)
                    ·
                      refine ⟨1937537606317026519684227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5166766950178737385824605 1937537606317026519684227)
                      ·
                        rfl

theorem cell23_3773341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_3773341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3773341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3773341 prefixEnd_3773341 := by exact prefixLift 3773341
  have htrace : WordTrace (prefixWord ++ tailWord_3773341) baseStart_3773341 baseEnd_3773341 := by
    simpa [prefixWord, tailWord_3773341, baseEnd_3773341] using wordTrace_append hprefix tailTrace_3773341
  have hstable : (prefixWord ++ tailWord_3773341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773341).length < 2 ^ (prefixWord ++ tailWord_3773341).sum := by decide
  have hdescent : baseEnd_3773341 < baseStart_3773341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773353 : List Nat := [1, 2, 1, 1, 1, 1, 16]
def baseStart_3773353 : Nat := 118140960795 + 3773353 * 2 ^ 59
def prefixEnd_3773353 : Nat := 4983230072969 + 3 ^ 40 * 3773353 * 2
def baseEnd_3773353 : Nat := 23920293433146672502891

theorem tailTrace_3773353 : CollatzResearch.WordTrace tailWord_3773353 prefixEnd_3773353 23920293433146672502891 := by
  unfold tailWord_3773353
  simp only [CollatzResearch.WordTrace]
  refine ⟨137625490298793993231228713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91750326865862662154152475 137625490298793993231228713)
  ·
    refine ⟨103219117724095494923421535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137625490298793993231228713 103219117724095494923421535)
    ·
      refine ⟨154828676586143242385132303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103219117724095494923421535 154828676586143242385132303)
      ·
        refine ⟨232243014879214863577698455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154828676586143242385132303 232243014879214863577698455)
        ·
          refine ⟨348364522318822295366547683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232243014879214863577698455 348364522318822295366547683)
          ·
            refine ⟨522546783478233443049821525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348364522318822295366547683 522546783478233443049821525)
            ·
              refine ⟨23920293433146672502891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 16 522546783478233443049821525 23920293433146672502891)
              ·
                rfl

theorem cell23_3773353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 16].length) (baseStart_3773353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3773353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3773353 prefixEnd_3773353 := by exact prefixLift 3773353
  have htrace : WordTrace (prefixWord ++ tailWord_3773353) baseStart_3773353 baseEnd_3773353 := by
    simpa [prefixWord, tailWord_3773353, baseEnd_3773353] using wordTrace_append hprefix tailTrace_3773353
  have hstable : (prefixWord ++ tailWord_3773353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773353).length < 2 ^ (prefixWord ++ tailWord_3773353).sum := by decide
  have hdescent : baseEnd_3773353 < baseStart_3773353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773387 : List Nat := [1, 1, 1, 1, 3, 7, 2, 7]
def baseStart_3773387 : Nat := 118140960795 + 3773387 * 2 ^ 59
def prefixEnd_3773387 : Nat := 4983230072969 + 3 ^ 40 * 3773387 * 2
def baseEnd_3773387 : Nat := 71761526904708642211445

theorem tailTrace_3773387 : CollatzResearch.WordTrace tailWord_3773387 prefixEnd_3773387 71761526904708642211445 := by
  unfold tailWord_3773387
  simp only [CollatzResearch.WordTrace]
  refine ⟨137626730380670817037966415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91751153587113878025310943 137626730380670817037966415)
  ·
    refine ⟨206440095571006225556949623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137626730380670817037966415 206440095571006225556949623)
    ·
      refine ⟨309660143356509338335424435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206440095571006225556949623 309660143356509338335424435)
      ·
        refine ⟨464490215034764007503136653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309660143356509338335424435 464490215034764007503136653)
        ·
          refine ⟨174183830638036502813676245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 464490215034764007503136653 174183830638036502813676245)
          ·
            refine ⟨4082433530578980534695537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 174183830638036502813676245 4082433530578980534695537)
            ·
              refine ⟨3061825147934235401021653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4082433530578980534695537 3061825147934235401021653)
              ·
                refine ⟨71761526904708642211445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3061825147934235401021653 71761526904708642211445)
                ·
                  rfl

theorem cell23_3773387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 7].length) (baseStart_3773387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3773387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3773387 prefixEnd_3773387 := by exact prefixLift 3773387
  have htrace : WordTrace (prefixWord ++ tailWord_3773387) baseStart_3773387 baseEnd_3773387 := by
    simpa [prefixWord, tailWord_3773387, baseEnd_3773387] using wordTrace_append hprefix tailTrace_3773387
  have hstable : (prefixWord ++ tailWord_3773387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773387).length < 2 ^ (prefixWord ++ tailWord_3773387).sum := by decide
  have hdescent : baseEnd_3773387 < baseStart_3773387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773415 : List Nat := [1, 1, 5, 2, 2, 2, 3, 2, 1, 2, 2]
def baseStart_3773415 : Nat := 118140960795 + 3773415 * 2 ^ 59
def prefixEnd_3773415 : Nat := 4983230072969 + 3 ^ 40 * 3773415 * 2
def baseEnd_3773415 : Nat := 1937575603885459230158887

theorem tailTrace_3773415 : CollatzResearch.WordTrace tailWord_3773415 prefixEnd_3773415 1937575603885459230158887 := by
  unfold tailWord_3773415
  simp only [CollatzResearch.WordTrace]
  refine ⟨137627751624569377819985699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91751834416379585213323799 137627751624569377819985699)
  ·
    refine ⟨206441627436854066729978549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137627751624569377819985699 206441627436854066729978549)
    ·
      refine ⟨19353902572205068755935489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 206441627436854066729978549 19353902572205068755935489)
      ·
        refine ⟨14515426929153801566951617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19353902572205068755935489 14515426929153801566951617)
        ·
          refine ⟨10886570196865351175213713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14515426929153801566951617 10886570196865351175213713)
          ·
            refine ⟨8164927647649013381410285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10886570196865351175213713 8164927647649013381410285)
            ·
              refine ⟨3061847867868380018028857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8164927647649013381410285 3061847867868380018028857)
              ·
                refine ⟨2296385900901285013521643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3061847867868380018028857 2296385900901285013521643)
                ·
                  refine ⟨3444578851351927520282465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2296385900901285013521643 3444578851351927520282465)
                  ·
                    refine ⟨2583434138513945640211849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3444578851351927520282465 2583434138513945640211849)
                    ·
                      refine ⟨1937575603885459230158887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2583434138513945640211849 1937575603885459230158887)
                      ·
                        rfl

theorem cell23_3773415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_3773415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3773415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3773415 prefixEnd_3773415 := by exact prefixLift 3773415
  have htrace : WordTrace (prefixWord ++ tailWord_3773415) baseStart_3773415 baseEnd_3773415 := by
    simpa [prefixWord, tailWord_3773415, baseEnd_3773415] using wordTrace_append hprefix tailTrace_3773415
  have hstable : (prefixWord ++ tailWord_3773415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773415).length < 2 ^ (prefixWord ++ tailWord_3773415).sum := by decide
  have hdescent : baseEnd_3773415 < baseStart_3773415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773441 : List Nat := [1, 2, 4, 1, 2, 2, 3, 2, 1, 3, 2]
def baseStart_3773441 : Nat := 118140960795 + 3773441 * 2 ^ 59
def prefixEnd_3773441 : Nat := 4983230072969 + 3 ^ 40 * 3773441 * 2
def baseEnd_3773441 : Nat := 1937588954382476128433767

theorem tailTrace_3773441 : CollatzResearch.WordTrace tailWord_3773441 prefixEnd_3773441 1937588954382476128433767 := by
  unfold tailWord_3773441
  simp only [CollatzResearch.WordTrace]
  refine ⟨137628699922475184260432177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91752466614983456173621451 137628699922475184260432177)
  ·
    refine ⟨103221524941856388195324133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137628699922475184260432177 103221524941856388195324133)
    ·
      refine ⟨19354035926598072786623275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103221524941856388195324133 19354035926598072786623275)
      ·
        refine ⟨29031053889897109179934913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19354035926598072786623275 29031053889897109179934913)
        ·
          refine ⟨21773290417422831884951185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29031053889897109179934913 21773290417422831884951185)
          ·
            refine ⟨16329967813067123913713389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21773290417422831884951185 16329967813067123913713389)
            ·
              refine ⟨6123737929900171467642521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16329967813067123913713389 6123737929900171467642521)
              ·
                refine ⟨4592803447425128600731891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6123737929900171467642521 4592803447425128600731891)
                ·
                  refine ⟨6889205171137692901097837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4592803447425128600731891 6889205171137692901097837)
                  ·
                    refine ⟨2583451939176634837911689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6889205171137692901097837 2583451939176634837911689)
                    ·
                      refine ⟨1937588954382476128433767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2583451939176634837911689 1937588954382476128433767)
                      ·
                        rfl

theorem cell23_3773441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_3773441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3773441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3773441 prefixEnd_3773441 := by exact prefixLift 3773441
  have htrace : WordTrace (prefixWord ++ tailWord_3773441) baseStart_3773441 baseEnd_3773441 := by
    simpa [prefixWord, tailWord_3773441, baseEnd_3773441] using wordTrace_append hprefix tailTrace_3773441
  have hstable : (prefixWord ++ tailWord_3773441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773441).length < 2 ^ (prefixWord ++ tailWord_3773441).sum := by decide
  have hdescent : baseEnd_3773441 < baseStart_3773441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773454 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2]
def baseStart_3773454 : Nat := 118140960795 + 3773454 * 2 ^ 59
def prefixEnd_3773454 : Nat := 4983230072969 + 3 ^ 40 * 3773454 * 2
def baseEnd_3773454 : Nat := 1937595629630984577571207

theorem tailTrace_3773454 : CollatzResearch.WordTrace tailWord_3773454 prefixEnd_3773454 1937595629630984577571207 := by
  unfold tailWord_3773454
  simp only [CollatzResearch.WordTrace]
  refine ⟨17203646758928510935081927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91752782714285391653770277 17203646758928510935081927)
  ·
    refine ⟨25805470138392766402622891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17203646758928510935081927 25805470138392766402622891)
    ·
      refine ⟨38708205207589149603934337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25805470138392766402622891 38708205207589149603934337)
      ·
        refine ⟨29031153905691862202950753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38708205207589149603934337 29031153905691862202950753)
        ·
          refine ⟨21773365429268896652213065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29031153905691862202950753 21773365429268896652213065)
          ·
            refine ⟨16330024071951672489159799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21773365429268896652213065 16330024071951672489159799)
            ·
              refine ⟨24495036107927508733739699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16330024071951672489159799 24495036107927508733739699)
              ·
                refine ⟨36742554161891263100609549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24495036107927508733739699 36742554161891263100609549)
                ·
                  refine ⟨13778457810709223662728581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36742554161891263100609549 13778457810709223662728581)
                  ·
                    refine ⟨2583460839507979436761609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13778457810709223662728581 2583460839507979436761609)
                    ·
                      refine ⟨1937595629630984577571207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2583460839507979436761609 1937595629630984577571207)
                      ·
                        rfl

theorem cell23_3773454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_3773454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3773454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3773454 prefixEnd_3773454 := by exact prefixLift 3773454
  have htrace : WordTrace (prefixWord ++ tailWord_3773454) baseStart_3773454 baseEnd_3773454 := by
    simpa [prefixWord, tailWord_3773454, baseEnd_3773454] using wordTrace_append hprefix tailTrace_3773454
  have hstable : (prefixWord ++ tailWord_3773454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773454).length < 2 ^ (prefixWord ++ tailWord_3773454).sum := by decide
  have hdescent : baseEnd_3773454 < baseStart_3773454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773471 : List Nat := [1, 1, 2, 4, 1, 3, 1, 4, 2, 2, 2]
def baseStart_3773471 : Nat := 118140960795 + 3773471 * 2 ^ 59
def prefixEnd_3773471 : Nat := 4983230072969 + 3 ^ 40 * 3773471 * 2
def baseEnd_3773471 : Nat := 1937604358802111011058629

theorem tailTrace_3773471 : CollatzResearch.WordTrace tailWord_3773471 prefixEnd_3773471 1937604358802111011058629 := by
  unfold tailWord_3773471
  simp only [CollatzResearch.WordTrace]
  refine ⟨137629794112366499384024267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91753196074910999589349511 137629794112366499384024267)
  ·
    refine ⟨206444691168549749076036401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137629794112366499384024267 206444691168549749076036401)
    ·
      refine ⟨154833518376412311807027301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206444691168549749076036401 154833518376412311807027301)
      ·
        refine ⟨29031284695577308463817619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154833518376412311807027301 29031284695577308463817619)
        ·
          refine ⟨43546927043365962695726429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29031284695577308463817619 43546927043365962695726429)
          ·
            refine ⟨16330097641262236010897411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43546927043365962695726429 16330097641262236010897411)
            ·
              refine ⟨24495146461893354016346117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16330097641262236010897411 24495146461893354016346117)
              ·
                refine ⟨4592839961605003878064897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24495146461893354016346117 4592839961605003878064897)
                ·
                  refine ⟨3444629971203752908548673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4592839961605003878064897 3444629971203752908548673)
                  ·
                    refine ⟨2583472478402814681411505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3444629971203752908548673 2583472478402814681411505)
                    ·
                      refine ⟨1937604358802111011058629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2583472478402814681411505 1937604358802111011058629)
                      ·
                        rfl

theorem cell23_3773471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_3773471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3773471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3773471 prefixEnd_3773471 := by exact prefixLift 3773471
  have htrace : WordTrace (prefixWord ++ tailWord_3773471) baseStart_3773471 baseEnd_3773471 := by
    simpa [prefixWord, tailWord_3773471, baseEnd_3773471] using wordTrace_append hprefix tailTrace_3773471
  have hstable : (prefixWord ++ tailWord_3773471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773471).length < 2 ^ (prefixWord ++ tailWord_3773471).sum := by decide
  have hdescent : baseEnd_3773471 < baseStart_3773471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773494 : List Nat := [5, 1, 2, 1, 1, 3, 1, 2, 7]
def baseStart_3773494 : Nat := 118140960795 + 3773494 * 2 ^ 59
def prefixEnd_3773494 : Nat := 4983230072969 + 3 ^ 40 * 3773494 * 2
def baseEnd_3773494 : Nat := 215290685428573824563447

theorem tailTrace_3773494 : CollatzResearch.WordTrace tailWord_3773494 prefixEnd_3773494 215290685428573824563447 := by
  unfold tailWord_3773494
  simp only [CollatzResearch.WordTrace]
  refine ⟨8601914561955198394506971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91753755327522116208074357 8601914561955198394506971)
  ·
    refine ⟨12902871842932797591760457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8601914561955198394506971 12902871842932797591760457)
    ·
      refine ⟨9677153882199598193820343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12902871842932797591760457 9677153882199598193820343)
      ·
        refine ⟨14515730823299397290730515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9677153882199598193820343 14515730823299397290730515)
        ·
          refine ⟨21773596234949095936095773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14515730823299397290730515 21773596234949095936095773)
          ·
            refine ⟨8165098588105910976035915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21773596234949095936095773 8165098588105910976035915)
            ·
              refine ⟨12247647882158866464053873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8165098588105910976035915 12247647882158866464053873)
              ·
                refine ⟨9185735911619149848040405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12247647882158866464053873 9185735911619149848040405)
                ·
                  refine ⟨215290685428573824563447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9185735911619149848040405 215290685428573824563447)
                  ·
                    rfl

theorem cell23_3773494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_3773494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3773494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3773494 prefixEnd_3773494 := by exact prefixLift 3773494
  have htrace : WordTrace (prefixWord ++ tailWord_3773494) baseStart_3773494 baseEnd_3773494 := by
    simpa [prefixWord, tailWord_3773494, baseEnd_3773494] using wordTrace_append hprefix tailTrace_3773494
  have hstable : (prefixWord ++ tailWord_3773494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773494).length < 2 ^ (prefixWord ++ tailWord_3773494).sum := by decide
  have hdescent : baseEnd_3773494 < baseStart_3773494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773520 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 1, 10]
def baseStart_3773520 : Nat := 118140960795 + 3773520 * 2 ^ 59
def prefixEnd_3773520 : Nat := 4983230072969 + 3 ^ 40 * 3773520 * 2
def baseEnd_3773520 : Nat := 645876506451393773115301

theorem tailTrace_3773520 : CollatzResearch.WordTrace tailWord_3773520 prefixEnd_3773520 645876506451393773115301 := by
  unfold tailWord_3773520
  simp only [CollatzResearch.WordTrace]
  refine ⟨68815790644594490376279007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91754387526125987168372009 68815790644594490376279007)
  ·
    refine ⟨103223685966891735564418511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68815790644594490376279007 103223685966891735564418511)
    ·
      refine ⟨154835528950337603346627767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103223685966891735564418511 154835528950337603346627767)
      ·
        refine ⟨232253293425506405019941651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154835528950337603346627767 232253293425506405019941651)
        ·
          refine ⟨348379940138259607529912477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232253293425506405019941651 348379940138259607529912477)
          ·
            refine ⟨130642477551847352823717179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 348379940138259607529912477 130642477551847352823717179)
            ·
              refine ⟨195963716327771029235575769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130642477551847352823717179 195963716327771029235575769)
              ·
                refine ⟨146972787245828271926681827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195963716327771029235575769 146972787245828271926681827)
                ·
                  refine ⟨220459180868742407890022741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146972787245828271926681827 220459180868742407890022741)
                  ·
                    refine ⟨645876506451393773115301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 220459180868742407890022741 645876506451393773115301)
                    ·
                      rfl

theorem cell23_3773520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 10].length) (baseStart_3773520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3773520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3773520 prefixEnd_3773520 := by exact prefixLift 3773520
  have htrace : WordTrace (prefixWord ++ tailWord_3773520) baseStart_3773520 baseEnd_3773520 := by
    simpa [prefixWord, tailWord_3773520, baseEnd_3773520] using wordTrace_append hprefix tailTrace_3773520
  have hstable : (prefixWord ++ tailWord_3773520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773520).length < 2 ^ (prefixWord ++ tailWord_3773520).sum := by decide
  have hdescent : baseEnd_3773520 < baseStart_3773520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773527 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 4]
def baseStart_3773527 : Nat := 118140960795 + 3773527 * 2 ^ 59
def prefixEnd_3773527 : Nat := 4983230072969 + 3 ^ 40 * 3773527 * 2
def baseEnd_3773527 : Nat := 1937633113718762791958371

theorem tailTrace_3773527 : CollatzResearch.WordTrace tailWord_3773527 prefixEnd_3773527 1937633113718762791958371 := by
  unfold tailWord_3773527
  simp only [CollatzResearch.WordTrace]
  refine ⟨137631836600163620948062835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91754557733442413965375223 137631836600163620948062835)
  ·
    refine ⟨206447754900245431422094253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137631836600163620948062835 206447754900245431422094253)
    ·
      refine ⟨77417908087592036783285345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206447754900245431422094253 77417908087592036783285345)
      ·
        refine ⟨58063431065694027587464009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77417908087592036783285345 58063431065694027587464009)
        ·
          refine ⟨43547573299270520690598007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58063431065694027587464009 43547573299270520690598007)
          ·
            refine ⟨65321359948905781035897011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43547573299270520690598007 65321359948905781035897011)
            ·
              refine ⟨97982039923358671553845517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65321359948905781035897011 97982039923358671553845517)
              ·
                refine ⟨36743264971259501832692069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97982039923358671553845517 36743264971259501832692069)
                ·
                  refine ⟨6889362182111156593629763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36743264971259501832692069 6889362182111156593629763)
                  ·
                    refine ⟨10334043273166734890444645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6889362182111156593629763 10334043273166734890444645)
                    ·
                      refine ⟨1937633113718762791958371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10334043273166734890444645 1937633113718762791958371)
                      ·
                        rfl

theorem cell23_3773527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_3773527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3773527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3773527 prefixEnd_3773527 := by exact prefixLift 3773527
  have htrace : WordTrace (prefixWord ++ tailWord_3773527) baseStart_3773527 baseEnd_3773527 := by
    simpa [prefixWord, tailWord_3773527, baseEnd_3773527] using wordTrace_append hprefix tailTrace_3773527
  have hstable : (prefixWord ++ tailWord_3773527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773527).length < 2 ^ (prefixWord ++ tailWord_3773527).sum := by decide
  have hdescent : baseEnd_3773527 < baseStart_3773527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773554 : List Nat := [3, 2, 1, 2, 2, 1, 1, 4, 3, 4]
def baseStart_3773554 : Nat := 118140960795 + 3773554 * 2 ^ 59
def prefixEnd_3773554 : Nat := 4983230072969 + 3 ^ 40 * 3773554 * 2
def baseEnd_3773554 : Nat := 645882325898811395440249

theorem tailTrace_3773554 : CollatzResearch.WordTrace tailWord_3773554 prefixEnd_3773554 645882325898811395440249 := by
  unfold tailWord_3773554
  simp only [CollatzResearch.WordTrace]
  refine ⟨34408205342766451139823929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91755214247377203039530477 34408205342766451139823929)
  ·
    refine ⟨25806154007074838354867947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34408205342766451139823929 25806154007074838354867947)
    ·
      refine ⟨38709231010612257532301921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25806154007074838354867947 38709231010612257532301921)
      ·
        refine ⟨29031923257959193149226441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38709231010612257532301921 29031923257959193149226441)
        ·
          refine ⟨21773942443469394861919831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29031923257959193149226441 21773942443469394861919831)
          ·
            refine ⟨32660913665204092292879747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21773942443469394861919831 32660913665204092292879747)
            ·
              refine ⟨48991370497806138439319621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32660913665204092292879747 48991370497806138439319621)
              ·
                refine ⟨9185881968338650957372429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48991370497806138439319621 9185881968338650957372429)
                ·
                  refine ⟨3444705738126994109014661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9185881968338650957372429 3444705738126994109014661)
                  ·
                    refine ⟨645882325898811395440249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3444705738126994109014661 645882325898811395440249)
                    ·
                      rfl

theorem cell23_3773554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_3773554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3773554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3773554 prefixEnd_3773554 := by exact prefixLift 3773554
  have htrace : WordTrace (prefixWord ++ tailWord_3773554) baseStart_3773554 baseEnd_3773554 := by
    simpa [prefixWord, tailWord_3773554, baseEnd_3773554] using wordTrace_append hprefix tailTrace_3773554
  have hstable : (prefixWord ++ tailWord_3773554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773554).length < 2 ^ (prefixWord ++ tailWord_3773554).sum := by decide
  have hdescent : baseEnd_3773554 < baseStart_3773554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773564 : List Nat := [2, 2, 2, 1, 1, 3, 2, 3, 2, 2, 3]
def baseStart_3773564 : Nat := 118140960795 + 3773564 * 2 ^ 59
def prefixEnd_3773564 : Nat := 4983230072969 + 3 ^ 40 * 3773564 * 2
def baseEnd_3773564 : Nat := 1937652112502979147195701

theorem tailTrace_3773564 : CollatzResearch.WordTrace tailWord_3773564 prefixEnd_3773564 1937652112502979147195701 := by
  unfold tailWord_3773564
  simp only [CollatzResearch.WordTrace]
  refine ⟨68816593050514788133579873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91755457400686384178106497 68816593050514788133579873)
  ·
    refine ⟨51612444787886091100184905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68816593050514788133579873 51612444787886091100184905)
    ·
      refine ⟨38709333590914568325138679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51612444787886091100184905 38709333590914568325138679)
      ·
        refine ⟨58064000386371852487708019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38709333590914568325138679 58064000386371852487708019)
        ·
          refine ⟨87096000579557778731562029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58064000386371852487708019 87096000579557778731562029)
          ·
            refine ⟨32661000217334167024335761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87096000579557778731562029 32661000217334167024335761)
            ·
              refine ⟨24495750163000625268251821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32661000217334167024335761 24495750163000625268251821)
              ·
                refine ⟨9185906311125234475594433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24495750163000625268251821 9185906311125234475594433)
                ·
                  refine ⟨6889429733343925856695825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9185906311125234475594433 6889429733343925856695825)
                  ·
                    refine ⟨5167072300007944392521869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6889429733343925856695825 5167072300007944392521869)
                    ·
                      refine ⟨1937652112502979147195701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5167072300007944392521869 1937652112502979147195701)
                      ·
                        rfl

theorem cell23_3773564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_3773564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3773564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3773564 prefixEnd_3773564 := by exact prefixLift 3773564
  have htrace : WordTrace (prefixWord ++ tailWord_3773564) baseStart_3773564 baseEnd_3773564 := by
    simpa [prefixWord, tailWord_3773564, baseEnd_3773564] using wordTrace_append hprefix tailTrace_3773564
  have hstable : (prefixWord ++ tailWord_3773564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773564).length < 2 ^ (prefixWord ++ tailWord_3773564).sum := by decide
  have hdescent : baseEnd_3773564 < baseStart_3773564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773647 : List Nat := [1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 6]
def baseStart_3773647 : Nat := 118140960795 + 3773647 * 2 ^ 59
def prefixEnd_3773647 : Nat := 4983230072969 + 3 ^ 40 * 3773647 * 2
def baseEnd_3773647 : Nat := 1937694731397302322457819

theorem tailTrace_3773647 : CollatzResearch.WordTrace tailWord_3773647 prefixEnd_3773647 1937694731397302322457819 := by
  unfold tailWord_3773647
  simp only [CollatzResearch.WordTrace]
  refine ⟨137636213359728881442431195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91757475573152587628287463 137636213359728881442431195)
  ·
    refine ⟨206454320039593322163646793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137636213359728881442431195 206454320039593322163646793)
    ·
      refine ⟨154840740029694991622735095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206454320039593322163646793 154840740029694991622735095)
      ·
        refine ⟨232261110044542487434102643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154840740029694991622735095 232261110044542487434102643)
        ·
          refine ⟨348391665066813731151153965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232261110044542487434102643 348391665066813731151153965)
          ·
            refine ⟨130646874400055149181682737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 348391665066813731151153965 130646874400055149181682737)
            ·
              refine ⟨97985155800041361886262053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130646874400055149181682737 97985155800041361886262053)
              ·
                refine ⟨18372216712507755353674135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97985155800041361886262053 18372216712507755353674135)
                ·
                  refine ⟨27558325068761633030511203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18372216712507755353674135 27558325068761633030511203)
                  ·
                    refine ⟨41337487603142449545766805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27558325068761633030511203 41337487603142449545766805)
                    ·
                      refine ⟨1937694731397302322457819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41337487603142449545766805 1937694731397302322457819)
                      ·
                        rfl

theorem cell23_3773647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 6].length) (baseStart_3773647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3773647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3773647 prefixEnd_3773647 := by exact prefixLift 3773647
  have htrace : WordTrace (prefixWord ++ tailWord_3773647) baseStart_3773647 baseEnd_3773647 := by
    simpa [prefixWord, tailWord_3773647, baseEnd_3773647] using wordTrace_append hprefix tailTrace_3773647
  have hstable : (prefixWord ++ tailWord_3773647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773647).length < 2 ^ (prefixWord ++ tailWord_3773647).sum := by decide
  have hdescent : baseEnd_3773647 < baseStart_3773647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773664 : List Nat := [2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 4]
def baseStart_3773664 : Nat := 118140960795 + 3773664 * 2 ^ 59
def prefixEnd_3773664 : Nat := 4983230072969 + 3 ^ 40 * 3773664 * 2
def baseEnd_3773664 : Nat := 1937703460568428755945241

theorem tailTrace_3773664 : CollatzResearch.WordTrace tailWord_3773664 prefixEnd_3773664 1937703460568428755945241 := by
  unfold tailWord_3773664
  simp only [CollatzResearch.WordTrace]
  refine ⟨68818416700333646672900023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91757888933778195563866697 68818416700333646672900023)
  ·
    refine ⟨103227625050500470009350035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68818416700333646672900023 103227625050500470009350035)
    ·
      refine ⟨154841437575750705014025053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103227625050500470009350035 154841437575750705014025053)
      ·
        refine ⟨58065539090906514380259395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154841437575750705014025053 58065539090906514380259395)
        ·
          refine ⟨87098308636359771570389093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58065539090906514380259395 87098308636359771570389093)
          ·
            refine ⟨16330932869317457169447955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87098308636359771570389093 16330932869317457169447955)
            ·
              refine ⟨24496399303976185754171933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16330932869317457169447955 24496399303976185754171933)
              ·
                refine ⟨9186149738991069657814475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24496399303976185754171933 9186149738991069657814475)
                ·
                  refine ⟨13779224608486604486721713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9186149738991069657814475 13779224608486604486721713)
                  ·
                    refine ⟨10334418456364953365041285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13779224608486604486721713 10334418456364953365041285)
                    ·
                      refine ⟨1937703460568428755945241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10334418456364953365041285 1937703460568428755945241)
                      ·
                        rfl

theorem cell23_3773664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_3773664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3773664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3773664 prefixEnd_3773664 := by exact prefixLift 3773664
  have htrace : WordTrace (prefixWord ++ tailWord_3773664) baseStart_3773664 baseEnd_3773664 := by
    simpa [prefixWord, tailWord_3773664, baseEnd_3773664] using wordTrace_append hprefix tailTrace_3773664
  have hstable : (prefixWord ++ tailWord_3773664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773664).length < 2 ^ (prefixWord ++ tailWord_3773664).sum := by decide
  have hdescent : baseEnd_3773664 < baseStart_3773664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773687 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 4, 7]
def baseStart_3773687 : Nat := 118140960795 + 3773687 * 2 ^ 59
def prefixEnd_3773687 : Nat := 4983230072969 + 3 ^ 40 * 3773687 * 2
def baseEnd_3773687 : Nat := 645905090207827388652545

theorem tailTrace_3773687 : CollatzResearch.WordTrace tailWord_3773687 prefixEnd_3773687 645905090207827388652545 := by
  unfold tailWord_3773687
  simp only [CollatzResearch.WordTrace]
  refine ⟨137637672279583968273887315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91758448186389312182591543 137637672279583968273887315)
  ·
    refine ⟨206456508419375952410830973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137637672279583968273887315 206456508419375952410830973)
    ·
      refine ⟨77421190657265982154061615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206456508419375952410830973 77421190657265982154061615)
      ·
        refine ⟨116131785985898973231092423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77421190657265982154061615 116131785985898973231092423)
        ·
          refine ⟨174197678978848459846638635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116131785985898973231092423 174197678978848459846638635)
          ·
            refine ⟨261296518468272689769957953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174197678978848459846638635 261296518468272689769957953)
            ·
              refine ⟨195972388851204517327468465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261296518468272689769957953 195972388851204517327468465)
              ·
                refine ⟨146979291638403387995601349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195972388851204517327468465 146979291638403387995601349)
                ·
                  refine ⟨27558617182200635249175253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146979291638403387995601349 27558617182200635249175253)
                  ·
                    refine ⟨645905090207827388652545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27558617182200635249175253 645905090207827388652545)
                    ·
                      rfl

theorem cell23_3773687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 7].length) (baseStart_3773687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3773687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3773687 prefixEnd_3773687 := by exact prefixLift 3773687
  have htrace : WordTrace (prefixWord ++ tailWord_3773687) baseStart_3773687 baseEnd_3773687 := by
    simpa [prefixWord, tailWord_3773687, baseEnd_3773687] using wordTrace_append hprefix tailTrace_3773687
  have hstable : (prefixWord ++ tailWord_3773687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773687).length < 2 ^ (prefixWord ++ tailWord_3773687).sum := by decide
  have hdescent : baseEnd_3773687 < baseStart_3773687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773701 : List Nat := [1, 3, 1, 1, 2, 1, 5, 1, 4, 1, 3]
def baseStart_3773701 : Nat := 118140960795 + 3773701 * 2 ^ 59
def prefixEnd_3773701 : Nat := 4983230072969 + 3 ^ 40 * 3773701 * 2
def baseEnd_3773701 : Nat := 1937722459352645111182571

theorem tailTrace_3773701 : CollatzResearch.WordTrace tailWord_3773701 prefixEnd_3773701 1937722459352645111182571 := by
  unfold tailWord_3773701
  simp only [CollatzResearch.WordTrace]
  refine ⟨137638182901533248664896957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91758788601022165776597971 137638182901533248664896957)
  ·
    refine ⟨51614318588074968249336359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137638182901533248664896957 51614318588074968249336359)
    ·
      refine ⟨77421477882112452374004539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51614318588074968249336359 77421477882112452374004539)
      ·
        refine ⟨116132216823168678561006809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77421477882112452374004539 116132216823168678561006809)
        ·
          refine ⟨87099162617376508920755107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116132216823168678561006809 87099162617376508920755107)
          ·
            refine ⟨130648743926064763381132661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87099162617376508920755107 130648743926064763381132661)
            ·
              refine ⟨12248319743068571566981187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130648743926064763381132661 12248319743068571566981187)
              ·
                refine ⟨18372479614602857350471781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12248319743068571566981187 18372479614602857350471781)
                ·
                  refine ⟨3444839927738035753213459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18372479614602857350471781 3444839927738035753213459)
                  ·
                    refine ⟨5167259891607053629820189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3444839927738035753213459 5167259891607053629820189)
                    ·
                      refine ⟨1937722459352645111182571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5167259891607053629820189 1937722459352645111182571)
                      ·
                        rfl

theorem cell23_3773701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 4, 1, 3].length) (baseStart_3773701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3773701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3773701 prefixEnd_3773701 := by exact prefixLift 3773701
  have htrace : WordTrace (prefixWord ++ tailWord_3773701) baseStart_3773701 baseEnd_3773701 := by
    simpa [prefixWord, tailWord_3773701, baseEnd_3773701] using wordTrace_append hprefix tailTrace_3773701
  have hstable : (prefixWord ++ tailWord_3773701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773701).length < 2 ^ (prefixWord ++ tailWord_3773701).sum := by decide
  have hdescent : baseEnd_3773701 < baseStart_3773701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773724 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 2, 3, 4]
def baseStart_3773724 : Nat := 118140960795 + 3773724 * 2 ^ 59
def prefixEnd_3773724 : Nat := 4983230072969 + 3 ^ 40 * 3773724 * 2
def baseEnd_3773724 : Nat := 1937734269407698521194965

theorem tailTrace_3773724 : CollatzResearch.WordTrace tailWord_3773724 prefixEnd_3773724 1937734269407698521194965 := by
  unfold tailWord_3773724
  simp only [CollatzResearch.WordTrace]
  refine ⟨68819510890224961796492113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91759347853633282395322817 68819510890224961796492113)
  ·
    refine ⟨51614633167668721347369085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68819510890224961796492113 51614633167668721347369085)
    ·
      refine ⟨19355487437875770505263407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51614633167668721347369085 19355487437875770505263407)
      ·
        refine ⟨29033231156813655757895111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19355487437875770505263407 29033231156813655757895111)
        ·
          refine ⟨43549846735220483636842667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29033231156813655757895111 43549846735220483636842667)
          ·
            refine ⟨65324770102830725455264001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43549846735220483636842667 65324770102830725455264001)
            ·
              refine ⟨48993577577123044091448001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65324770102830725455264001 48993577577123044091448001)
              ·
                refine ⟨36745183182842283068586001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48993577577123044091448001 36745183182842283068586001)
                ·
                  refine ⟨27558887387131712301439501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36745183182842283068586001 27558887387131712301439501)
                  ·
                    refine ⟨10334582770174392113039813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27558887387131712301439501 10334582770174392113039813)
                    ·
                      refine ⟨1937734269407698521194965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10334582770174392113039813 1937734269407698521194965)
                      ·
                        rfl

theorem cell23_3773724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_3773724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3773724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3773724 prefixEnd_3773724 := by exact prefixLift 3773724
  have htrace : WordTrace (prefixWord ++ tailWord_3773724) baseStart_3773724 baseEnd_3773724 := by
    simpa [prefixWord, tailWord_3773724, baseEnd_3773724] using wordTrace_append hprefix tailTrace_3773724
  have hstable : (prefixWord ++ tailWord_3773724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773724).length < 2 ^ (prefixWord ++ tailWord_3773724).sum := by decide
  have hdescent : baseEnd_3773724 < baseStart_3773724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773744 : List Nat := [2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 5]
def baseStart_3773744 : Nat := 118140960795 + 3773744 * 2 ^ 59
def prefixEnd_3773744 : Nat := 4983230072969 + 3 ^ 40 * 3773744 * 2
def baseEnd_3773744 : Nat := 1937744539020788442944873

theorem tailTrace_3773744 : CollatzResearch.WordTrace tailWord_3773744 prefixEnd_3773744 1937744539020788442944873 := by
  unfold tailWord_3773744
  simp only [CollatzResearch.WordTrace]
  refine ⟨68819875620188733504356143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91759834160251644672474857 68819875620188733504356143)
  ·
    refine ⟨103229813430283100256534215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68819875620188733504356143 103229813430283100256534215)
    ·
      refine ⟨154844720145424650384801323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103229813430283100256534215 154844720145424650384801323)
      ·
        refine ⟨232267080218136975577201985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154844720145424650384801323 232267080218136975577201985)
        ·
          refine ⟨174200310163602731682901489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232267080218136975577201985 174200310163602731682901489)
          ·
            refine ⟨130650232622702048762176117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174200310163602731682901489 130650232622702048762176117)
            ·
              refine ⟨12248459308378317071454011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130650232622702048762176117 12248459308378317071454011)
              ·
                refine ⟨18372688962567475607181017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12248459308378317071454011 18372688962567475607181017)
                ·
                  refine ⟨13779516721925606705385763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18372688962567475607181017 13779516721925606705385763)
                  ·
                    refine ⟨20669275082888410058078645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13779516721925606705385763 20669275082888410058078645)
                    ·
                      refine ⟨1937744539020788442944873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20669275082888410058078645 1937744539020788442944873)
                      ·
                        rfl

theorem cell23_3773744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 5].length) (baseStart_3773744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3773744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3773744 prefixEnd_3773744 := by exact prefixLift 3773744
  have htrace : WordTrace (prefixWord ++ tailWord_3773744) baseStart_3773744 baseEnd_3773744 := by
    simpa [prefixWord, tailWord_3773744, baseEnd_3773744] using wordTrace_append hprefix tailTrace_3773744
  have hstable : (prefixWord ++ tailWord_3773744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773744).length < 2 ^ (prefixWord ++ tailWord_3773744).sum := by decide
  have hdescent : baseEnd_3773744 < baseStart_3773744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773841 : List Nat := [1, 2, 2, 1, 1, 1, 2, 6, 3, 4]
def baseStart_3773841 : Nat := 118140960795 + 3773841 * 2 ^ 59
def prefixEnd_3773841 : Nat := 4983230072969 + 3 ^ 40 * 3773841 * 2
def baseEnd_3773841 : Nat := 645931448881424854477309

theorem tailTrace_3773841 : CollatzResearch.WordTrace tailWord_3773841 prefixEnd_3773841 645931448881424854477309 := by
  unfold tailWord_3773841
  simp only [CollatzResearch.WordTrace]
  refine ⟨137643289121026052574993377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91762192747350701716662251 137643289121026052574993377)
  ·
    refine ⟨103232466840769539431245033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137643289121026052574993377 103232466840769539431245033)
    ·
      refine ⟨77424350130577154573433775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103232466840769539431245033 77424350130577154573433775)
      ·
        refine ⟨116136525195865731860150663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77424350130577154573433775 116136525195865731860150663)
        ·
          refine ⟨174204787793798597790225995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116136525195865731860150663 174204787793798597790225995)
          ·
            refine ⟨261307181690697896685338993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174204787793798597790225995 261307181690697896685338993)
            ·
              refine ⟨195980386268023422514004245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261307181690697896685338993 195980386268023422514004245)
              ·
                refine ⟨9186580606313597930343949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 195980386268023422514004245 9186580606313597930343949)
                ·
                  refine ⟨3444967727367599223878981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9186580606313597930343949 3444967727367599223878981)
                  ·
                    refine ⟨645931448881424854477309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3444967727367599223878981 645931448881424854477309)
                    ·
                      rfl

theorem cell23_3773841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 3, 4].length) (baseStart_3773841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3773841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3773841 prefixEnd_3773841 := by exact prefixLift 3773841
  have htrace : WordTrace (prefixWord ++ tailWord_3773841) baseStart_3773841 baseEnd_3773841 := by
    simpa [prefixWord, tailWord_3773841, baseEnd_3773841] using wordTrace_append hprefix tailTrace_3773841
  have hstable : (prefixWord ++ tailWord_3773841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773841).length < 2 ^ (prefixWord ++ tailWord_3773841).sum := by decide
  have hdescent : baseEnd_3773841 < baseStart_3773841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773848 : List Nat := [2, 1, 2, 5, 2, 1, 1, 1, 1, 3, 4]
def baseStart_3773848 : Nat := 118140960795 + 3773848 * 2 ^ 59
def prefixEnd_3773848 : Nat := 4983230072969 + 3 ^ 40 * 3773848 * 2
def baseEnd_3773848 : Nat := 1937797941008856036044395

theorem tailTrace_3773848 : CollatzResearch.WordTrace tailWord_3773848 prefixEnd_3773848 1937797941008856036044395 := by
  unfold tailWord_3773848
  simp only [CollatzResearch.WordTrace]
  refine ⟨68821772216000346385249099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91762362954667128513665465 68821772216000346385249099)
  ·
    refine ⟨103232658324000519577873649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68821772216000346385249099 103232658324000519577873649)
    ·
      refine ⟨77424493743000389683405237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103232658324000519577873649 77424493743000389683405237)
      ·
        refine ⟨7258546288406286532819241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77424493743000389683405237 7258546288406286532819241)
        ·
          refine ⟨5443909716304714899614431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7258546288406286532819241 5443909716304714899614431)
          ·
            refine ⟨8165864574457072349421647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5443909716304714899614431 8165864574457072349421647)
            ·
              refine ⟨12248796861685608524132471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8165864574457072349421647 12248796861685608524132471)
              ·
                refine ⟨18373195292528412786198707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12248796861685608524132471 18373195292528412786198707)
                ·
                  refine ⟨27559792938792619179298061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18373195292528412786198707 27559792938792619179298061)
                  ·
                    refine ⟨10334922352047232192236773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27559792938792619179298061 10334922352047232192236773)
                    ·
                      refine ⟨1937797941008856036044395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10334922352047232192236773 1937797941008856036044395)
                      ·
                        rfl

theorem cell23_3773848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_3773848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3773848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3773848 prefixEnd_3773848 := by exact prefixLift 3773848
  have htrace : WordTrace (prefixWord ++ tailWord_3773848) baseStart_3773848 baseEnd_3773848 := by
    simpa [prefixWord, tailWord_3773848, baseEnd_3773848] using wordTrace_append hprefix tailTrace_3773848
  have hstable : (prefixWord ++ tailWord_3773848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773848).length < 2 ^ (prefixWord ++ tailWord_3773848).sum := by decide
  have hdescent : baseEnd_3773848 < baseStart_3773848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3773925 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 4, 3, 2]
def baseStart_3773925 : Nat := 118140960795 + 3773925 * 2 ^ 59
def prefixEnd_3773925 : Nat := 4983230072969 + 3 ^ 40 * 3773925 * 2
def baseEnd_3773925 : Nat := 1937837479019252234781541

theorem tailTrace_3773925 : CollatzResearch.WordTrace tailWord_3773925 prefixEnd_3773925 1937837479019252234781541 := by
  unfold tailWord_3773925
  simp only [CollatzResearch.WordTrace]
  refine ⟨137646352852721734921051229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91764235235147823280700819 137646352852721734921051229)
  ·
    refine ⟨51617382319770650595394211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137646352852721734921051229 51617382319770650595394211)
    ·
      refine ⟨77426073479655975893091317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51617382319770650595394211 77426073479655975893091317)
      ·
        refine ⟨7258694388717747739977311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77426073479655975893091317 7258694388717747739977311)
        ·
          refine ⟨10888041583076621609965967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7258694388717747739977311 10888041583076621609965967)
          ·
            refine ⟨16332062374614932414948951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10888041583076621609965967 16332062374614932414948951)
            ·
              refine ⟨24498093561922398622423427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16332062374614932414948951 24498093561922398622423427)
              ·
                refine ⟨36747140342883597933635141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24498093561922398622423427 36747140342883597933635141)
                ·
                  refine ⟨6890088814290674612556589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36747140342883597933635141 6890088814290674612556589)
                  ·
                    refine ⟨2583783305359002979708721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6890088814290674612556589 2583783305359002979708721)
                    ·
                      refine ⟨1937837479019252234781541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2583783305359002979708721 1937837479019252234781541)
                      ·
                        rfl

theorem cell23_3773925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_3773925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3773925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3773925 prefixEnd_3773925 := by exact prefixLift 3773925
  have htrace : WordTrace (prefixWord ++ tailWord_3773925) baseStart_3773925 baseEnd_3773925 := by
    simpa [prefixWord, tailWord_3773925, baseEnd_3773925] using wordTrace_append hprefix tailTrace_3773925
  have hstable : (prefixWord ++ tailWord_3773925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3773925).length < 2 ^ (prefixWord ++ tailWord_3773925).sum := by decide
  have hdescent : baseEnd_3773925 < baseStart_3773925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3773925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774001 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 1, 4, 5]
def baseStart_3774001 : Nat := 118140960795 + 3774001 * 2 ^ 59
def prefixEnd_3774001 : Nat := 4983230072969 + 3 ^ 40 * 3774001 * 2
def baseEnd_3774001 : Nat := 1937876503548993937431191

theorem tailTrace_3774001 : CollatzResearch.WordTrace tailWord_3774001 prefixEnd_3774001 1937876503548993937431191 := by
  unfold tailWord_3774001
  simp only [CollatzResearch.WordTrace]
  refine ⟨137649124800446399900817857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91766083200297599933878571 137649124800446399900817857)
  ·
    refine ⟨103236843600334799925613393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137649124800446399900817857 103236843600334799925613393)
    ·
      refine ⟨77427632700251099944210045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103236843600334799925613393 77427632700251099944210045)
      ·
        refine ⟨29035362262594162479078767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77427632700251099944210045 29035362262594162479078767)
        ·
          refine ⟨43553043393891243718618151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29035362262594162479078767 43553043393891243718618151)
          ·
            refine ⟨65329565090836865577927227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43553043393891243718618151 65329565090836865577927227)
            ·
              refine ⟨97994347636255298366890841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65329565090836865577927227 97994347636255298366890841)
              ·
                refine ⟨73495760727191473775168131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97994347636255298366890841 73495760727191473775168131)
                ·
                  refine ⟨110243641090787210662752197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73495760727191473775168131 110243641090787210662752197)
                  ·
                    refine ⟨20670682704522601999266037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 110243641090787210662752197 20670682704522601999266037)
                    ·
                      refine ⟨1937876503548993937431191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20670682704522601999266037 1937876503548993937431191)
                      ·
                        rfl

theorem cell23_3774001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_3774001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774001 prefixEnd_3774001 := by exact prefixLift 3774001
  have htrace : WordTrace (prefixWord ++ tailWord_3774001) baseStart_3774001 baseEnd_3774001 := by
    simpa [prefixWord, tailWord_3774001, baseEnd_3774001] using wordTrace_append hprefix tailTrace_3774001
  have hstable : (prefixWord ++ tailWord_3774001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774001).length < 2 ^ (prefixWord ++ tailWord_3774001).sum := by decide
  have hdescent : baseEnd_3774001 < baseStart_3774001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774005 : List Nat := [1, 3, 3, 1, 1, 4, 2, 1, 1, 3, 3]
def baseStart_3774005 : Nat := 118140960795 + 3774005 * 2 ^ 59
def prefixEnd_3774005 : Nat := 4983230072969 + 3 ^ 40 * 3774005 * 2
def baseEnd_3774005 : Nat := 1937878557471611921781173

theorem tailTrace_3774005 : CollatzResearch.WordTrace tailWord_3774005 prefixEnd_3774005 1937878557471611921781173 := by
  unfold tailWord_3774005
  simp only [CollatzResearch.WordTrace]
  refine ⟨137649270692431908583963469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91766180461621272389308979 137649270692431908583963469)
  ·
    refine ⟨51618476509661965718986301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137649270692431908583963469 51618476509661965718986301)
    ·
      refine ⟨19356928691123237144619863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51618476509661965718986301 19356928691123237144619863)
      ·
        refine ⟨29035393036684855716929795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19356928691123237144619863 29035393036684855716929795)
        ·
          refine ⟨43553089555027283575394693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29035393036684855716929795 43553089555027283575394693)
          ·
            refine ⟨8166204291567615670386505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43553089555027283575394693 8166204291567615670386505)
            ·
              refine ⟨6124653218675711752789879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8166204291567615670386505 6124653218675711752789879)
              ·
                refine ⟨9186979828013567629184819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6124653218675711752789879 9186979828013567629184819)
                ·
                  refine ⟨13780469742020351443777229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9186979828013567629184819 13780469742020351443777229)
                  ·
                    refine ⟨5167676153257631791416461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13780469742020351443777229 5167676153257631791416461)
                    ·
                      refine ⟨1937878557471611921781173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5167676153257631791416461 1937878557471611921781173)
                      ·
                        rfl

theorem cell23_3774005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_3774005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774005 prefixEnd_3774005 := by exact prefixLift 3774005
  have htrace : WordTrace (prefixWord ++ tailWord_3774005) baseStart_3774005 baseEnd_3774005 := by
    simpa [prefixWord, tailWord_3774005, baseEnd_3774005] using wordTrace_append hprefix tailTrace_3774005
  have hstable : (prefixWord ++ tailWord_3774005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774005).length < 2 ^ (prefixWord ++ tailWord_3774005).sum := by decide
  have hdescent : baseEnd_3774005 < baseStart_3774005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774015 : List Nat := [1, 1, 2, 2, 3, 3, 2, 1, 3, 3, 2]
def baseStart_3774015 : Nat := 118140960795 + 3774015 * 2 ^ 59
def prefixEnd_3774015 : Nat := 4983230072969 + 3 ^ 40 * 3774015 * 2
def baseEnd_3774015 : Nat := 1937883692278156882656127

theorem tailTrace_3774015 : CollatzResearch.WordTrace tailWord_3774015 prefixEnd_3774015 1937883692278156882656127 := by
  unfold tailWord_3774015
  simp only [CollatzResearch.WordTrace]
  refine ⟨137649635422395680291827499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91766423614930453527884999 137649635422395680291827499)
  ·
    refine ⟨206474453133593520437741249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137649635422395680291827499 206474453133593520437741249)
    ·
      refine ⟨154855839850195140328305937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206474453133593520437741249 154855839850195140328305937)
      ·
        refine ⟨116141879887646355246229453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154855839850195140328305937 116141879887646355246229453)
        ·
          refine ⟨43553204957867383217336045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116141879887646355246229453 43553204957867383217336045)
          ·
            refine ⟨16332451859200268706501017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43553204957867383217336045 16332451859200268706501017)
            ·
              refine ⟨12249338894400201529875763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16332451859200268706501017 12249338894400201529875763)
              ·
                refine ⟨18374008341600302294813645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12249338894400201529875763 18374008341600302294813645)
                ·
                  refine ⟨6890253128100113360555117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18374008341600302294813645 6890253128100113360555117)
                  ·
                    refine ⟨2583844923037542510208169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6890253128100113360555117 2583844923037542510208169)
                    ·
                      refine ⟨1937883692278156882656127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2583844923037542510208169 1937883692278156882656127)
                      ·
                        rfl

theorem cell23_3774015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 3, 2].length) (baseStart_3774015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774015 prefixEnd_3774015 := by exact prefixLift 3774015
  have htrace : WordTrace (prefixWord ++ tailWord_3774015) baseStart_3774015 baseEnd_3774015 := by
    simpa [prefixWord, tailWord_3774015, baseEnd_3774015] using wordTrace_append hprefix tailTrace_3774015
  have hstable : (prefixWord ++ tailWord_3774015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774015).length < 2 ^ (prefixWord ++ tailWord_3774015).sum := by decide
  have hdescent : baseEnd_3774015 < baseStart_3774015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774021 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 1, 8]
def baseStart_3774021 : Nat := 118140960795 + 3774021 * 2 ^ 59
def prefixEnd_3774021 : Nat := 4983230072969 + 3 ^ 40 * 3774021 * 2
def baseEnd_3774021 : Nat := 645962257720694619727033

theorem tailTrace_3774021 : CollatzResearch.WordTrace tailWord_3774021 prefixEnd_3774021 645962257720694619727033 := by
  unfold tailWord_3774021
  simp only [CollatzResearch.WordTrace]
  refine ⟨137649854260373943316545917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91766569506915962211030611 137649854260373943316545917)
  ·
    refine ⟨51618695347640228743704719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137649854260373943316545917 51618695347640228743704719)
    ·
      refine ⟨77428043021460343115557079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51618695347640228743704719 77428043021460343115557079)
      ·
        refine ⟨116142064532190514673335619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77428043021460343115557079 116142064532190514673335619)
        ·
          refine ⟨174213096798285772010003429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116142064532190514673335619 174213096798285772010003429)
          ·
            refine ⟨32664955649678582251875643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174213096798285772010003429 32664955649678582251875643)
            ·
              refine ⟨48997433474517873377813465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32664955649678582251875643 48997433474517873377813465)
              ·
                refine ⟨36748075105888405033360099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48997433474517873377813465 36748075105888405033360099)
                ·
                  refine ⟨55122112658832607550040149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36748075105888405033360099 55122112658832607550040149)
                  ·
                    refine ⟨645962257720694619727033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55122112658832607550040149 645962257720694619727033)
                    ·
                      rfl

theorem cell23_3774021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 8].length) (baseStart_3774021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774021 prefixEnd_3774021 := by exact prefixLift 3774021
  have htrace : WordTrace (prefixWord ++ tailWord_3774021) baseStart_3774021 baseEnd_3774021 := by
    simpa [prefixWord, tailWord_3774021, baseEnd_3774021] using wordTrace_append hprefix tailTrace_3774021
  have hstable : (prefixWord ++ tailWord_3774021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774021).length < 2 ^ (prefixWord ++ tailWord_3774021).sum := by decide
  have hdescent : baseEnd_3774021 < baseStart_3774021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774031 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 5]
def baseStart_3774031 : Nat := 118140960795 + 3774031 * 2 ^ 59
def prefixEnd_3774031 : Nat := 4983230072969 + 3 ^ 40 * 3774031 * 2
def baseEnd_3774031 : Nat := 1937891907968628820056053

theorem tailTrace_3774031 : CollatzResearch.WordTrace tailWord_3774031 prefixEnd_3774031 1937891907968628820056053 := by
  unfold tailWord_3774031
  simp only [CollatzResearch.WordTrace]
  refine ⟨137650218990337715024409947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91766812660225143349606631 137650218990337715024409947)
  ·
    refine ⟨206475328485506572536614921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137650218990337715024409947 206475328485506572536614921)
    ·
      refine ⟨154856496364129929402461191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206475328485506572536614921 154856496364129929402461191)
      ·
        refine ⟨232284744546194894103691787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154856496364129929402461191 232284744546194894103691787)
        ·
          refine ⟨348427116819292341155537681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232284744546194894103691787 348427116819292341155537681)
          ·
            refine ⟨261320337614469255866653261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348427116819292341155537681 261320337614469255866653261)
            ·
              refine ⟨97995126605425970949994973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261320337614469255866653261 97995126605425970949994973)
              ·
                refine ⟨36748172477034739106248115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97995126605425970949994973 36748172477034739106248115)
                ·
                  refine ⟨55122258715552108659372173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36748172477034739106248115 55122258715552108659372173)
                  ·
                    refine ⟨20670847018332040747264565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55122258715552108659372173 20670847018332040747264565)
                    ·
                      refine ⟨1937891907968628820056053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20670847018332040747264565 1937891907968628820056053)
                      ·
                        rfl

theorem cell23_3774031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 5].length) (baseStart_3774031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774031 prefixEnd_3774031 := by exact prefixLift 3774031
  have htrace : WordTrace (prefixWord ++ tailWord_3774031) baseStart_3774031 baseEnd_3774031 := by
    simpa [prefixWord, tailWord_3774031, baseEnd_3774031] using wordTrace_append hprefix tailTrace_3774031
  have hstable : (prefixWord ++ tailWord_3774031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774031).length < 2 ^ (prefixWord ++ tailWord_3774031).sum := by decide
  have hdescent : baseEnd_3774031 < baseStart_3774031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774135 : List Nat := [1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 4]
def baseStart_3774135 : Nat := 118140960795 + 3774135 * 2 ^ 59
def prefixEnd_3774135 : Nat := 4983230072969 + 3 ^ 40 * 3774135 * 2
def baseEnd_3774135 : Nat := 1937945309956696413155575

theorem tailTrace_3774135 : CollatzResearch.WordTrace tailWord_3774135 prefixEnd_3774135 1937945309956696413155575 := by
  unfold tailWord_3774135
  simp only [CollatzResearch.WordTrace]
  refine ⟨137654012181960940786195859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91769341454640627190797239 137654012181960940786195859)
  ·
    refine ⟨206481018272941411179293789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137654012181960940786195859 206481018272941411179293789)
    ·
      refine ⟨77430381852353029192235171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206481018272941411179293789 77430381852353029192235171)
      ·
        refine ⟨116145572778529543788352757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77430381852353029192235171 116145572778529543788352757)
        ·
          refine ⟨10888647447987144730158071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116145572778529543788352757 10888647447987144730158071)
          ·
            refine ⟨16332971171980717095237107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10888647447987144730158071 16332971171980717095237107)
            ·
              refine ⟨24499456757971075642855661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16332971171980717095237107 24499456757971075642855661)
              ·
                refine ⟨9187296284239153366070873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24499456757971075642855661 9187296284239153366070873)
                ·
                  refine ⟨6890472213179365024553155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9187296284239153366070873 6890472213179365024553155)
                  ·
                    refine ⟨10335708319769047536829733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6890472213179365024553155 10335708319769047536829733)
                    ·
                      refine ⟨1937945309956696413155575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10335708319769047536829733 1937945309956696413155575)
                      ·
                        rfl

theorem cell23_3774135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 4].length) (baseStart_3774135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774135 prefixEnd_3774135 := by exact prefixLift 3774135
  have htrace : WordTrace (prefixWord ++ tailWord_3774135) baseStart_3774135 baseEnd_3774135 := by
    simpa [prefixWord, tailWord_3774135, baseEnd_3774135] using wordTrace_append hprefix tailTrace_3774135
  have hstable : (prefixWord ++ tailWord_3774135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774135).length < 2 ^ (prefixWord ++ tailWord_3774135).sum := by decide
  have hdescent : baseEnd_3774135 < baseStart_3774135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774189 : List Nat := [1, 5, 1, 2, 1, 4, 1, 1, 2, 2, 3]
def baseStart_3774189 : Nat := 118140960795 + 3774189 * 2 ^ 59
def prefixEnd_3774189 : Nat := 4983230072969 + 3 ^ 40 * 3774189 * 2
def baseEnd_3774189 : Nat := 1937973037912039201880327

theorem tailTrace_3774189 : CollatzResearch.WordTrace tailWord_3774189 prefixEnd_3774189 1937973037912039201880327 := by
  unfold tailWord_3774189
  simp only [CollatzResearch.WordTrace]
  refine ⟨137655981723765308008661621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91770654482510205339107747 137655981723765308008661621)
  ·
    refine ⟨12905248286602997625812027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137655981723765308008661621 12905248286602997625812027)
    ·
      refine ⟨19357872429904496438718041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12905248286602997625812027 19357872429904496438718041)
      ·
        refine ⟨14518404322428372329038531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19357872429904496438718041 14518404322428372329038531)
        ·
          refine ⟨21777606483642558493557797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14518404322428372329038531 21777606483642558493557797)
          ·
            refine ⟨4083301215682979717542087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21777606483642558493557797 4083301215682979717542087)
            ·
              refine ⟨6124951823524469576313131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4083301215682979717542087 6124951823524469576313131)
              ·
                refine ⟨9187427735286704364469697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6124951823524469576313131 9187427735286704364469697)
                ·
                  refine ⟨6890570801465028273352273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9187427735286704364469697 6890570801465028273352273)
                  ·
                    refine ⟨5167928101098771205014205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6890570801465028273352273 5167928101098771205014205)
                    ·
                      refine ⟨1937973037912039201880327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5167928101098771205014205 1937973037912039201880327)
                      ·
                        rfl

theorem cell23_3774189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_3774189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774189 prefixEnd_3774189 := by exact prefixLift 3774189
  have htrace : WordTrace (prefixWord ++ tailWord_3774189) baseStart_3774189 baseEnd_3774189 := by
    simpa [prefixWord, tailWord_3774189, baseEnd_3774189] using wordTrace_append hprefix tailTrace_3774189
  have hstable : (prefixWord ++ tailWord_3774189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774189).length < 2 ^ (prefixWord ++ tailWord_3774189).sum := by decide
  have hdescent : baseEnd_3774189 < baseStart_3774189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774219 : List Nat := [1, 1, 1, 1, 5, 1, 4, 4, 1, 1, 3]
def baseStart_3774219 : Nat := 118140960795 + 3774219 * 2 ^ 59
def prefixEnd_3774219 : Nat := 4983230072969 + 3 ^ 40 * 3774219 * 2
def baseEnd_3774219 : Nat := 1937988442331674084505189

theorem tailTrace_3774219 : CollatzResearch.WordTrace tailWord_3774219 prefixEnd_3774219 1937988442331674084505189 := by
  unfold tailWord_3774219
  simp only [CollatzResearch.WordTrace]
  refine ⟨137657075913656623132253711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91771383942437748754835807 137657075913656623132253711)
  ·
    refine ⟨206485613870484934698380567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137657075913656623132253711 206485613870484934698380567)
    ·
      refine ⟨309728420805727402047570851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206485613870484934698380567 309728420805727402047570851)
      ·
        refine ⟨464592631208591103071356277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309728420805727402047570851 464592631208591103071356277)
        ·
          refine ⟨43555559175805415912939651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 464592631208591103071356277 43555559175805415912939651)
          ·
            refine ⟨65333338763708123869409477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43555559175805415912939651 65333338763708123869409477)
            ·
              refine ⟨12250001018195273225514277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65333338763708123869409477 12250001018195273225514277)
              ·
                refine ⟨2296875190911613729783927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12250001018195273225514277 2296875190911613729783927)
                ·
                  refine ⟨3445312786367420594675891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2296875190911613729783927 3445312786367420594675891)
                  ·
                    refine ⟨5167969179551130892013837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3445312786367420594675891 5167969179551130892013837)
                    ·
                      refine ⟨1937988442331674084505189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5167969179551130892013837 1937988442331674084505189)
                      ·
                        rfl

theorem cell23_3774219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 4, 1, 1, 3].length) (baseStart_3774219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774219 prefixEnd_3774219 := by exact prefixLift 3774219
  have htrace : WordTrace (prefixWord ++ tailWord_3774219) baseStart_3774219 baseEnd_3774219 := by
    simpa [prefixWord, tailWord_3774219, baseEnd_3774219] using wordTrace_append hprefix tailTrace_3774219
  have hstable : (prefixWord ++ tailWord_3774219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774219).length < 2 ^ (prefixWord ++ tailWord_3774219).sum := by decide
  have hdescent : baseEnd_3774219 < baseStart_3774219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774242 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 2, 6, 2]
def baseStart_3774242 : Nat := 118140960795 + 3774242 * 2 ^ 59
def prefixEnd_3774242 : Nat := 4983230072969 + 3 ^ 40 * 3774242 * 2
def baseEnd_3774242 : Nat := 1938000252386727494517583

theorem tailTrace_3774242 : CollatzResearch.WordTrace tailWord_3774242 prefixEnd_3774242 1938000252386727494517583 := by
  unfold tailWord_3774242
  simp only [CollatzResearch.WordTrace]
  refine ⟨34414478698143324515085245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91771943195048865373560653 34414478698143324515085245)
  ·
    refine ⟨12905429511803746693156967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34414478698143324515085245 12905429511803746693156967)
    ·
      refine ⟨19358144267705620039735451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12905429511803746693156967 19358144267705620039735451)
      ·
        refine ⟨29037216401558430059603177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19358144267705620039735451 29037216401558430059603177)
        ·
          refine ⟨21777912301168822544702383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29037216401558430059603177 21777912301168822544702383)
          ·
            refine ⟨32666868451753233817053575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21777912301168822544702383 32666868451753233817053575)
            ·
              refine ⟨49000302677629850725580363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32666868451753233817053575 49000302677629850725580363)
              ·
                refine ⟨73500454016444776088370545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49000302677629850725580363 73500454016444776088370545)
                ·
                  refine ⟨55125340512333582066277909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73500454016444776088370545 55125340512333582066277909)
                  ·
                    refine ⟨2584000336515636659356777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55125340512333582066277909 2584000336515636659356777)
                    ·
                      refine ⟨1938000252386727494517583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2584000336515636659356777 1938000252386727494517583)
                      ·
                        rfl

theorem cell23_3774242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_3774242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774242 prefixEnd_3774242 := by exact prefixLift 3774242
  have htrace : WordTrace (prefixWord ++ tailWord_3774242) baseStart_3774242 baseEnd_3774242 := by
    simpa [prefixWord, tailWord_3774242, baseEnd_3774242] using wordTrace_append hprefix tailTrace_3774242
  have hstable : (prefixWord ++ tailWord_3774242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774242).length < 2 ^ (prefixWord ++ tailWord_3774242).sum := by decide
  have hdescent : baseEnd_3774242 < baseStart_3774242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774370 : List Nat := [3, 3, 1, 2, 3, 2, 2, 1, 1, 3, 2]
def baseStart_3774370 : Nat := 118140960795 + 3774370 * 2 ^ 59
def prefixEnd_3774370 : Nat := 4983230072969 + 3 ^ 40 * 3774370 * 2
def baseEnd_3774370 : Nat := 1938065977910502993716995

theorem tailTrace_3774370 : CollatzResearch.WordTrace tailWord_3774370 prefixEnd_3774370 1938065977910502993716995 := by
  unfold tailWord_3774370
  simp only [CollatzResearch.WordTrace]
  refine ⟨34415645834027393980250141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91775055557406383947333709 34415645834027393980250141)
  ·
    refine ⟨12905867187760272742593803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34415645834027393980250141 12905867187760272742593803)
    ·
      refine ⟨19358800781640409113890705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12905867187760272742593803 19358800781640409113890705)
      ·
        refine ⟨14519100586230306835418029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19358800781640409113890705 14519100586230306835418029)
        ·
          refine ⟨5444662719836365063281761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14519100586230306835418029 5444662719836365063281761)
          ·
            refine ⟨4083497039877273797461321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5444662719836365063281761 4083497039877273797461321)
            ·
              refine ⟨3062622779907955348095991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4083497039877273797461321 3062622779907955348095991)
              ·
                refine ⟨4593934169861933022143987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3062622779907955348095991 4593934169861933022143987)
                ·
                  refine ⟨6890901254792899533215981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4593934169861933022143987 6890901254792899533215981)
                  ·
                    refine ⟨2584087970547337324955993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6890901254792899533215981 2584087970547337324955993)
                    ·
                      refine ⟨1938065977910502993716995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2584087970547337324955993 1938065977910502993716995)
                      ·
                        rfl

theorem cell23_3774370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_3774370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774370 prefixEnd_3774370 := by exact prefixLift 3774370
  have htrace : WordTrace (prefixWord ++ tailWord_3774370) baseStart_3774370 baseEnd_3774370 := by
    simpa [prefixWord, tailWord_3774370, baseEnd_3774370] using wordTrace_append hprefix tailTrace_3774370
  have hstable : (prefixWord ++ tailWord_3774370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774370).length < 2 ^ (prefixWord ++ tailWord_3774370).sum := by decide
  have hdescent : baseEnd_3774370 < baseStart_3774370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774389 : List Nat := [1, 3, 3, 2, 1, 2, 2, 4, 5]
def baseStart_3774389 : Nat := 118140960795 + 3774389 * 2 ^ 59
def prefixEnd_3774389 : Nat := 4983230072969 + 3 ^ 40 * 3774389 * 2
def baseEnd_3774389 : Nat := 215341748226993157708823

theorem tailTrace_3774389 : CollatzResearch.WordTrace tailWord_3774389 prefixEnd_3774389 215341748226993157708823 := by
  unfold tailWord_3774389
  simp only [CollatzResearch.WordTrace]
  refine ⟨137663276323040742165942221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91775517548693828110628147 137663276323040742165942221)
  ·
    refine ⟨51623728621140278312228333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137663276323040742165942221 51623728621140278312228333)
    ·
      refine ⟨19358898232927604367085625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51623728621140278312228333 19358898232927604367085625)
      ·
        refine ⟨14519173674695703275314219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19358898232927604367085625 14519173674695703275314219)
        ·
          refine ⟨21778760512043554912971329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14519173674695703275314219 21778760512043554912971329)
          ·
            refine ⟨16334070384032666184728497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21778760512043554912971329 16334070384032666184728497)
            ·
              refine ⟨12250552788024499638546373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16334070384032666184728497 12250552788024499638546373)
              ·
                refine ⟨2296978647754593682227445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12250552788024499638546373 2296978647754593682227445)
                ·
                  refine ⟨215341748226993157708823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2296978647754593682227445 215341748226993157708823)
                  ·
                    rfl

theorem cell23_3774389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 4, 5].length) (baseStart_3774389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774389 prefixEnd_3774389 := by exact prefixLift 3774389
  have htrace : WordTrace (prefixWord ++ tailWord_3774389) baseStart_3774389 baseEnd_3774389 := by
    simpa [prefixWord, tailWord_3774389, baseEnd_3774389] using wordTrace_append hprefix tailTrace_3774389
  have hstable : (prefixWord ++ tailWord_3774389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774389).length < 2 ^ (prefixWord ++ tailWord_3774389).sum := by decide
  have hdescent : baseEnd_3774389 < baseStart_3774389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774415 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 2, 8]
def baseStart_3774415 : Nat := 118140960795 + 3774415 * 2 ^ 59
def prefixEnd_3774415 : Nat := 4983230072969 + 3 ^ 40 * 3774415 * 2
def baseEnd_3774415 : Nat := 646029694846651772551429

theorem tailTrace_3774415 : CollatzResearch.WordTrace tailWord_3774415 prefixEnd_3774415 646029694846651772551429 := by
  unfold tailWord_3774415
  simp only [CollatzResearch.WordTrace]
  refine ⟨137664224620946548606388699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91776149747297699070925799 137664224620946548606388699)
  ·
    refine ⟨206496336931419822909583049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137664224620946548606388699 206496336931419822909583049)
    ·
      refine ⟨154872252698564867182187287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206496336931419822909583049 154872252698564867182187287)
      ·
        refine ⟨232308379047847300773280931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154872252698564867182187287 232308379047847300773280931)
        ·
          refine ⟨348462568571770951159921397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232308379047847300773280931 348462568571770951159921397)
          ·
            refine ⟨32668365803603526671242631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 348462568571770951159921397 32668365803603526671242631)
            ·
              refine ⟨49002548705405290006863947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32668365803603526671242631 49002548705405290006863947)
              ·
                refine ⟨73503823058107935010295921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49002548705405290006863947 73503823058107935010295921)
                ·
                  refine ⟨55127867293580951257721941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73503823058107935010295921 55127867293580951257721941)
                  ·
                    refine ⟨646029694846651772551429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55127867293580951257721941 646029694846651772551429)
                    ·
                      rfl

theorem cell23_3774415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 8].length) (baseStart_3774415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774415 prefixEnd_3774415 := by exact prefixLift 3774415
  have htrace : WordTrace (prefixWord ++ tailWord_3774415) baseStart_3774415 baseEnd_3774415 := by
    simpa [prefixWord, tailWord_3774415, baseEnd_3774415] using wordTrace_append hprefix tailTrace_3774415
  have hstable : (prefixWord ++ tailWord_3774415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774415).length < 2 ^ (prefixWord ++ tailWord_3774415).sum := by decide
  have hdescent : baseEnd_3774415 < baseStart_3774415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774432 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 5, 4]
def baseStart_3774432 : Nat := 118140960795 + 3774432 * 2 ^ 59
def prefixEnd_3774432 : Nat := 4983230072969 + 3 ^ 40 * 3774432 * 2
def baseEnd_3774432 : Nat := 646032604570360583713903

theorem tailTrace_3774432 : CollatzResearch.WordTrace tailWord_3774432 prefixEnd_3774432 646032604570360583713903 := by
  unfold tailWord_3774432
  simp only [CollatzResearch.WordTrace]
  refine ⟨68832422330942480254878775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91776563107923307006505033 68832422330942480254878775)
  ·
    refine ⟨103248633496413720382318163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68832422330942480254878775 103248633496413720382318163)
    ·
      refine ⟨154872950244620580573477245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103248633496413720382318163 154872950244620580573477245)
      ·
        refine ⟨58077356341732717715053967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154872950244620580573477245 58077356341732717715053967)
        ·
          refine ⟨87116034512599076572580951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58077356341732717715053967 87116034512599076572580951)
          ·
            refine ⟨130674051768898614858871427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87116034512599076572580951 130674051768898614858871427)
            ·
              refine ⟨196011077653347922288307141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130674051768898614858871427 196011077653347922288307141)
              ·
                refine ⟨36752077060002735429057589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 196011077653347922288307141 36752077060002735429057589)
                ·
                  refine ⟨3445507224375256446474149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36752077060002735429057589 3445507224375256446474149)
                  ·
                    refine ⟨646032604570360583713903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3445507224375256446474149 646032604570360583713903)
                    ·
                      rfl

theorem cell23_3774432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 5, 4].length) (baseStart_3774432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774432 prefixEnd_3774432 := by exact prefixLift 3774432
  have htrace : WordTrace (prefixWord ++ tailWord_3774432) baseStart_3774432 baseEnd_3774432 := by
    simpa [prefixWord, tailWord_3774432, baseEnd_3774432] using wordTrace_append hprefix tailTrace_3774432
  have hstable : (prefixWord ++ tailWord_3774432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774432).length < 2 ^ (prefixWord ++ tailWord_3774432).sum := by decide
  have hdescent : baseEnd_3774432 < baseStart_3774432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774552 : List Nat := [2, 1, 2, 2, 1, 5, 10]
def baseStart_3774552 : Nat := 118140960795 + 3774552 * 2 ^ 59
def prefixEnd_3774552 : Nat := 4983230072969 + 3 ^ 40 * 3774552 * 2
def baseEnd_3774552 : Nat := 23927894214686682489397

theorem tailTrace_3774552 : CollatzResearch.WordTrace tailWord_3774552 prefixEnd_3774552 23927894214686682489397 := by
  unfold tailWord_3774552
  simp only [CollatzResearch.WordTrace]
  refine ⟨68834610710725110502062955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91779480947633480669417273 68834610710725110502062955)
  ·
    refine ⟨103251916066087665753094433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68834610710725110502062955 103251916066087665753094433)
    ·
      refine ⟨77438937049565749314820825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103251916066087665753094433 77438937049565749314820825)
      ·
        refine ⟨58079202787174311986115619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77438937049565749314820825 58079202787174311986115619)
        ·
          refine ⟨87118804180761467979173429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58079202787174311986115619 87118804180761467979173429)
          ·
            refine ⟨8167387891946387623047509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87118804180761467979173429 8167387891946387623047509)
            ·
              refine ⟨23927894214686682489397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8167387891946387623047509 23927894214686682489397)
              ·
                rfl

theorem cell23_3774552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 10].length) (baseStart_3774552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774552 prefixEnd_3774552 := by exact prefixLift 3774552
  have htrace : WordTrace (prefixWord ++ tailWord_3774552) baseStart_3774552 baseEnd_3774552 := by
    simpa [prefixWord, tailWord_3774552, baseEnd_3774552] using wordTrace_append hprefix tailTrace_3774552
  have hstable : (prefixWord ++ tailWord_3774552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774552).length < 2 ^ (prefixWord ++ tailWord_3774552).sum := by decide
  have hdescent : baseEnd_3774552 < baseStart_3774552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774556 : List Nat := [2, 2, 4, 1, 1, 3, 1, 1, 4, 4]
def baseStart_3774556 : Nat := 118140960795 + 3774556 * 2 ^ 59
def prefixEnd_3774556 : Nat := 4983230072969 + 3 ^ 40 * 3774556 * 2
def baseEnd_3774556 : Nat := 646053828437413088663713

theorem tailTrace_3774556 : CollatzResearch.WordTrace tailWord_3774556 prefixEnd_3774556 646053828437413088663713 := by
  unfold tailWord_3774556
  simp only [CollatzResearch.WordTrace]
  refine ⟨68834683656717864843635761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91779578208957153124847681 68834683656717864843635761)
  ·
    refine ⟨51626012742538398632726821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68834683656717864843635761 51626012742538398632726821)
    ·
      refine ⟨9679877389225949743636279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51626012742538398632726821 9679877389225949743636279)
      ·
        refine ⟨14519816083838924615454419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9679877389225949743636279 14519816083838924615454419)
        ·
          refine ⟨21779724125758386923181629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14519816083838924615454419 21779724125758386923181629)
          ·
            refine ⟨8167396547159395096193111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21779724125758386923181629 8167396547159395096193111)
            ·
              refine ⟨12251094820739092644289667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8167396547159395096193111 12251094820739092644289667)
              ·
                refine ⟨18376642231108638966434501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12251094820739092644289667 18376642231108638966434501)
                ·
                  refine ⟨3445620418332869806206469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18376642231108638966434501 3445620418332869806206469)
                  ·
                    refine ⟨646053828437413088663713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3445620418332869806206469 646053828437413088663713)
                    ·
                      rfl

theorem cell23_3774556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_3774556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774556 prefixEnd_3774556 := by exact prefixLift 3774556
  have htrace : WordTrace (prefixWord ++ tailWord_3774556) baseStart_3774556 baseEnd_3774556 := by
    simpa [prefixWord, tailWord_3774556, baseEnd_3774556] using wordTrace_append hprefix tailTrace_3774556
  have hstable : (prefixWord ++ tailWord_3774556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774556).length < 2 ^ (prefixWord ++ tailWord_3774556).sum := by decide
  have hdescent : baseEnd_3774556 < baseStart_3774556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774573 : List Nat := [1, 5, 1, 1, 2, 1, 5, 1, 2, 4]
def baseStart_3774573 : Nat := 118140960795 + 3774573 * 2 ^ 59
def prefixEnd_3774573 : Nat := 4983230072969 + 3 ^ 40 * 3774573 * 2
def baseEnd_3774573 : Nat := 646056738161121899826187

theorem tailTrace_3774573 : CollatzResearch.WordTrace tailWord_3774573 prefixEnd_3774573 646056738161121899826187 := by
  unfold tailWord_3774573
  simp only [CollatzResearch.WordTrace]
  refine ⟨137669987354374141590640373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91779991569582761060426915 137669987354374141590640373)
  ·
    refine ⟨12906561314472575774122535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137669987354374141590640373 12906561314472575774122535)
    ·
      refine ⟨19359841971708863661183803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12906561314472575774122535 19359841971708863661183803)
      ·
        refine ⟨29039762957563295491775705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19359841971708863661183803 29039762957563295491775705)
        ·
          refine ⟨21779822218172471618831779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29039762957563295491775705 21779822218172471618831779)
          ·
            refine ⟨32669733327258707428247669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21779822218172471618831779 32669733327258707428247669)
            ·
              refine ⟨3062787499430503821398219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32669733327258707428247669 3062787499430503821398219)
              ·
                refine ⟨4594181249145755732097329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3062787499430503821398219 4594181249145755732097329)
                ·
                  refine ⟨3445635936859316799072997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4594181249145755732097329 3445635936859316799072997)
                  ·
                    refine ⟨646056738161121899826187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3445635936859316799072997 646056738161121899826187)
                    ·
                      rfl

theorem cell23_3774573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_3774573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774573 prefixEnd_3774573 := by exact prefixLift 3774573
  have htrace : WordTrace (prefixWord ++ tailWord_3774573) baseStart_3774573 baseEnd_3774573 := by
    simpa [prefixWord, tailWord_3774573, baseEnd_3774573] using wordTrace_append hprefix tailTrace_3774573
  have hstable : (prefixWord ++ tailWord_3774573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774573).length < 2 ^ (prefixWord ++ tailWord_3774573).sum := by decide
  have hdescent : baseEnd_3774573 < baseStart_3774573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774576 : List Nat := [2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 4]
def baseStart_3774576 : Nat := 118140960795 + 3774576 * 2 ^ 59
def prefixEnd_3774576 : Nat := 4983230072969 + 3 ^ 40 * 3774576 * 2
def baseEnd_3774576 : Nat := 1938171754925329187741047

theorem tailTrace_3774576 : CollatzResearch.WordTrace tailWord_3774576 prefixEnd_3774576 1938171754925329187741047 := by
  unfold tailWord_3774576
  simp only [CollatzResearch.WordTrace]
  refine ⟨68835048386681636551499791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91780064515575515401999721 68835048386681636551499791)
  ·
    refine ⟨103252572580022454827249687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68835048386681636551499791 103252572580022454827249687)
    ·
      refine ⟨154878858870033682240874531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103252572580022454827249687 154878858870033682240874531)
      ·
        refine ⟨232318288305050523361311797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154878858870033682240874531 232318288305050523361311797)
        ·
          refine ⟨21779839528598486565122981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 232318288305050523361311797 21779839528598486565122981)
          ·
            refine ⟨4083719911612216230960559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21779839528598486565122981 4083719911612216230960559)
            ·
              refine ⟨6125579867418324346440839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4083719911612216230960559 6125579867418324346440839)
              ·
                refine ⟨9188369801127486519661259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6125579867418324346440839 9188369801127486519661259)
                ·
                  refine ⟨13782554701691229779491889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9188369801127486519661259 13782554701691229779491889)
                  ·
                    refine ⟨10336916026268422334618917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13782554701691229779491889 10336916026268422334618917)
                    ·
                      refine ⟨1938171754925329187741047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10336916026268422334618917 1938171754925329187741047)
                      ·
                        rfl

theorem cell23_3774576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 4].length) (baseStart_3774576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774576 prefixEnd_3774576 := by exact prefixLift 3774576
  have htrace : WordTrace (prefixWord ++ tailWord_3774576) baseStart_3774576 baseEnd_3774576 := by
    simpa [prefixWord, tailWord_3774576, baseEnd_3774576] using wordTrace_append hprefix tailTrace_3774576
  have hstable : (prefixWord ++ tailWord_3774576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774576).length < 2 ^ (prefixWord ++ tailWord_3774576).sum := by decide
  have hdescent : baseEnd_3774576 < baseStart_3774576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774596 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 6, 1, 3]
def baseStart_3774596 : Nat := 118140960795 + 3774596 * 2 ^ 59
def prefixEnd_3774596 : Nat := 4983230072969 + 3 ^ 40 * 3774596 * 2
def baseEnd_3774596 : Nat := 1938182024538419109490955

theorem tailTrace_3774596 : CollatzResearch.WordTrace tailWord_3774596 prefixEnd_3774596 1938182024538419109490955 := by
  unfold tailWord_3774596
  simp only [CollatzResearch.WordTrace]
  refine ⟨68835413116645408259363821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91780550822193877679151761 68835413116645408259363821)
  ·
    refine ⟨25813279918742028097261433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68835413116645408259363821 25813279918742028097261433)
    ·
      refine ⟨19359959939056521072946075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25813279918742028097261433 19359959939056521072946075)
      ·
        refine ⟨29039939908584781609419113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19359959939056521072946075 29039939908584781609419113)
        ·
          refine ⟨21779954931438586207064335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29039939908584781609419113 21779954931438586207064335)
          ·
            refine ⟨32669932397157879310596503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21779954931438586207064335 32669932397157879310596503)
            ·
              refine ⟨49004898595736818965894755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32669932397157879310596503 49004898595736818965894755)
              ·
                refine ⟨73507347893605228448842133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49004898595736818965894755 73507347893605228448842133)
                ·
                  refine ⟨3445656932512745083539475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73507347893605228448842133 3445656932512745083539475)
                  ·
                    refine ⟨5168485398769117625309213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3445656932512745083539475 5168485398769117625309213)
                    ·
                      refine ⟨1938182024538419109490955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5168485398769117625309213 1938182024538419109490955)
                      ·
                        rfl

theorem cell23_3774596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_3774596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774596 prefixEnd_3774596 := by exact prefixLift 3774596
  have htrace : WordTrace (prefixWord ++ tailWord_3774596) baseStart_3774596 baseEnd_3774596 := by
    simpa [prefixWord, tailWord_3774596, baseEnd_3774596] using wordTrace_append hprefix tailTrace_3774596
  have hstable : (prefixWord ++ tailWord_3774596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774596).length < 2 ^ (prefixWord ++ tailWord_3774596).sum := by decide
  have hdescent : baseEnd_3774596 < baseStart_3774596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774597 : List Nat := [1, 3, 1, 1, 5, 3, 1, 3, 1, 2, 2]
def baseStart_3774597 : Nat := 118140960795 + 3774597 * 2 ^ 59
def prefixEnd_3774597 : Nat := 4983230072969 + 3 ^ 40 * 3774597 * 2
def baseEnd_3774597 : Nat := 1938182538019073605578451

theorem tailTrace_3774597 : CollatzResearch.WordTrace tailWord_3774597 prefixEnd_3774597 1938182538019073605578451 := by
  unfold tailWord_3774597
  simp only [CollatzResearch.WordTrace]
  refine ⟨137670862706287193689514045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91780575137524795793009363 137670862706287193689514045)
  ·
    refine ⟨51626573514857697633567767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137670862706287193689514045 51626573514857697633567767)
    ·
      refine ⟨77439860272286546450351651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51626573514857697633567767 77439860272286546450351651)
      ·
        refine ⟨116159790408429819675527477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77439860272286546450351651 116159790408429819675527477)
        ·
          refine ⟨10889980350790295594580701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116159790408429819675527477 10889980350790295594580701)
          ·
            refine ⟨4083742631546360847967763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10889980350790295594580701 4083742631546360847967763)
            ·
              refine ⟨6125613947319541271951645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4083742631546360847967763 6125613947319541271951645)
              ·
                refine ⟨2297105230244827976981867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6125613947319541271951645 2297105230244827976981867)
                ·
                  refine ⟨3445657845367241965472801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2297105230244827976981867 3445657845367241965472801)
                  ·
                    refine ⟨2584243384025431474104601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3445657845367241965472801 2584243384025431474104601)
                    ·
                      refine ⟨1938182538019073605578451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2584243384025431474104601 1938182538019073605578451)
                      ·
                        rfl

theorem cell23_3774597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 3, 1, 2, 2].length) (baseStart_3774597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774597 prefixEnd_3774597 := by exact prefixLift 3774597
  have htrace : WordTrace (prefixWord ++ tailWord_3774597) baseStart_3774597 baseEnd_3774597 := by
    simpa [prefixWord, tailWord_3774597, baseEnd_3774597] using wordTrace_append hprefix tailTrace_3774597
  have hstable : (prefixWord ++ tailWord_3774597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774597).length < 2 ^ (prefixWord ++ tailWord_3774597).sum := by decide
  have hdescent : baseEnd_3774597 < baseStart_3774597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774670 : List Nat := [4, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2]
def baseStart_3774670 : Nat := 118140960795 + 3774670 * 2 ^ 59
def prefixEnd_3774670 : Nat := 4983230072969 + 3 ^ 40 * 3774670 * 2
def baseEnd_3774670 : Nat := 1938220022106851819965615

theorem tailTrace_3774670 : CollatzResearch.WordTrace tailWord_3774670 prefixEnd_3774670 1938220022106851819965615 := by
  unfold tailWord_3774670
  simp only [CollatzResearch.WordTrace]
  refine ⟨17209190654377840894615183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91782350156681818104614309 17209190654377840894615183)
  ·
    refine ⟨25813785981566761341922775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17209190654377840894615183 25813785981566761341922775)
    ·
      refine ⟨38720678972350142012884163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25813785981566761341922775 38720678972350142012884163)
      ·
        refine ⟨58081018458525213019326245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38720678972350142012884163 58081018458525213019326245)
        ·
          refine ⟨10890190960973477441123671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58081018458525213019326245 10890190960973477441123671)
          ·
            refine ⟨16335286441460216161685507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10890190960973477441123671 16335286441460216161685507)
            ·
              refine ⟨24502929662190324242528261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16335286441460216161685507 24502929662190324242528261)
              ·
                refine ⟨4594299311660685795474049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24502929662190324242528261 4594299311660685795474049)
                ·
                  refine ⟨3445724483745514346605537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4594299311660685795474049 3445724483745514346605537)
                  ·
                    refine ⟨2584293362809135759954153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3445724483745514346605537 2584293362809135759954153)
                    ·
                      refine ⟨1938220022106851819965615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2584293362809135759954153 1938220022106851819965615)
                      ·
                        rfl

theorem cell23_3774670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2].length) (baseStart_3774670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774670 prefixEnd_3774670 := by exact prefixLift 3774670
  have htrace : WordTrace (prefixWord ++ tailWord_3774670) baseStart_3774670 baseEnd_3774670 := by
    simpa [prefixWord, tailWord_3774670, baseEnd_3774670] using wordTrace_append hprefix tailTrace_3774670
  have hstable : (prefixWord ++ tailWord_3774670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774670).length < 2 ^ (prefixWord ++ tailWord_3774670).sum := by decide
  have hdescent : baseEnd_3774670 < baseStart_3774670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774689 : List Nat := [1, 2, 3, 1, 3, 1, 2, 2, 1, 7]
def baseStart_3774689 : Nat := 118140960795 + 3774689 * 2 ^ 59
def prefixEnd_3774689 : Nat := 4983230072969 + 3 ^ 40 * 3774689 * 2
def baseEnd_3774689 : Nat := 646076592746429081876009

theorem tailTrace_3774689 : CollatzResearch.WordTrace tailWord_3774689 prefixEnd_3774689 646076592746429081876009 := by
  unfold tailWord_3774689
  simp only [CollatzResearch.WordTrace]
  refine ⟨137674218221953893401863121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91782812147969262267908747 137674218221953893401863121)
  ·
    refine ⟨103255663666465420051397341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137674218221953893401863121 103255663666465420051397341)
    ·
      refine ⟨38720873874924532519274003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103255663666465420051397341 38720873874924532519274003)
      ·
        refine ⟨58081310812386798778911005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38720873874924532519274003 58081310812386798778911005)
        ·
          refine ⟨21780491554645049542091627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58081310812386798778911005 21780491554645049542091627)
          ·
            refine ⟨32670737331967574313137441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21780491554645049542091627 32670737331967574313137441)
            ·
              refine ⟨24503052998975680734853081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32670737331967574313137441 24503052998975680734853081)
              ·
                refine ⟨18377289749231760551139811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24503052998975680734853081 18377289749231760551139811)
                ·
                  refine ⟨27565934623847640826709717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18377289749231760551139811 27565934623847640826709717)
                  ·
                    refine ⟨646076592746429081876009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27565934623847640826709717 646076592746429081876009)
                    ·
                      rfl

theorem cell23_3774689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_3774689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774689 prefixEnd_3774689 := by exact prefixLift 3774689
  have htrace : WordTrace (prefixWord ++ tailWord_3774689) baseStart_3774689 baseEnd_3774689 := by
    simpa [prefixWord, tailWord_3774689, baseEnd_3774689] using wordTrace_append hprefix tailTrace_3774689
  have hstable : (prefixWord ++ tailWord_3774689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774689).length < 2 ^ (prefixWord ++ tailWord_3774689).sum := by decide
  have hdescent : baseEnd_3774689 < baseStart_3774689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774706 : List Nat := [3, 2, 1, 3, 2, 2, 1, 1, 1, 7]
def baseStart_3774706 : Nat := 118140960795 + 3774706 * 2 ^ 59
def prefixEnd_3774706 : Nat := 4983230072969 + 3 ^ 40 * 3774706 * 2
def baseEnd_3774706 : Nat := 646079502470137893038483

theorem tailTrace_3774706 : CollatzResearch.WordTrace tailWord_3774706 prefixEnd_3774706 646079502470137893038483 := by
  unfold tailWord_3774706
  simp only [CollatzResearch.WordTrace]
  refine ⟨34418709565723076326307993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91783225508594870203487981 34418709565723076326307993)
  ·
    refine ⟨25814032174292307244730995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34418709565723076326307993 25814032174292307244730995)
    ·
      refine ⟨38721048261438460867096493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25814032174292307244730995 38721048261438460867096493)
      ·
        refine ⟨14520393098039422825161185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38721048261438460867096493 14520393098039422825161185)
        ·
          refine ⟨10890294823529567118870889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14520393098039422825161185 10890294823529567118870889)
          ·
            refine ⟨8167721117647175339153167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10890294823529567118870889 8167721117647175339153167)
            ·
              refine ⟨12251581676470763008729751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8167721117647175339153167 12251581676470763008729751)
              ·
                refine ⟨18377372514706144513094627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12251581676470763008729751 18377372514706144513094627)
                ·
                  refine ⟨27566058772059216769641941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18377372514706144513094627 27566058772059216769641941)
                  ·
                    refine ⟨646079502470137893038483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27566058772059216769641941 646079502470137893038483)
                    ·
                      rfl

theorem cell23_3774706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_3774706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774706 prefixEnd_3774706 := by exact prefixLift 3774706
  have htrace : WordTrace (prefixWord ++ tailWord_3774706) baseStart_3774706 baseEnd_3774706 := by
    simpa [prefixWord, tailWord_3774706, baseEnd_3774706] using wordTrace_append hprefix tailTrace_3774706
  have hstable : (prefixWord ++ tailWord_3774706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774706).length < 2 ^ (prefixWord ++ tailWord_3774706).sum := by decide
  have hdescent : baseEnd_3774706 < baseStart_3774706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774743 : List Nat := [1, 1, 3, 4, 1, 2, 2, 1, 2, 4, 2]
def baseStart_3774743 : Nat := 118140960795 + 3774743 * 2 ^ 59
def prefixEnd_3774743 : Nat := 4983230072969 + 3 ^ 40 * 3774743 * 2
def baseEnd_3774743 : Nat := 1938257506194630034352779

theorem tailTrace_3774743 : CollatzResearch.WordTrace tailWord_3774743 prefixEnd_3774743 1938257506194630034352779 := by
  unfold tailWord_3774743
  simp only [CollatzResearch.WordTrace]
  refine ⟨137676187763758260624328883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91784125175838840416219255 137676187763758260624328883)
  ·
    refine ⟨206514281645637390936493325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137676187763758260624328883 206514281645637390936493325)
    ·
      refine ⟨77442855617114021601184997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206514281645637390936493325 77442855617114021601184997)
      ·
        refine ⟨14520535428208879050222187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77442855617114021601184997 14520535428208879050222187)
        ·
          refine ⟨21780803142313318575333281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14520535428208879050222187 21780803142313318575333281)
          ·
            refine ⟨16335602356734988931499961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21780803142313318575333281 16335602356734988931499961)
            ·
              refine ⟨12251701767551241698624971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16335602356734988931499961 12251701767551241698624971)
              ·
                refine ⟨18377552651326862547937457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12251701767551241698624971 18377552651326862547937457)
                ·
                  refine ⟨13783164488495146910953093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18377552651326862547937457 13783164488495146910953093)
                  ·
                    refine ⟨2584343341592840045803705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13783164488495146910953093 2584343341592840045803705)
                    ·
                      refine ⟨1938257506194630034352779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2584343341592840045803705 1938257506194630034352779)
                      ·
                        rfl

theorem cell23_3774743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_3774743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774743 prefixEnd_3774743 := by exact prefixLift 3774743
  have htrace : WordTrace (prefixWord ++ tailWord_3774743) baseStart_3774743 baseEnd_3774743 := by
    simpa [prefixWord, tailWord_3774743, baseEnd_3774743] using wordTrace_append hprefix tailTrace_3774743
  have hstable : (prefixWord ++ tailWord_3774743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774743).length < 2 ^ (prefixWord ++ tailWord_3774743).sum := by decide
  have hdescent : baseEnd_3774743 < baseStart_3774743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774789 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 4, 1, 7]
def baseStart_3774789 : Nat := 118140960795 + 3774789 * 2 ^ 59
def prefixEnd_3774789 : Nat := 4983230072969 + 3 ^ 40 * 3774789 * 2
def baseEnd_3774789 : Nat := 1938281126304736854377567

theorem tailTrace_3774789 : CollatzResearch.WordTrace tailWord_3774789 prefixEnd_3774789 1938281126304736854377567 := by
  unfold tailWord_3774789
  simp only [CollatzResearch.WordTrace]
  refine ⟨137677865521591610480503421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91785243681061073653668947 137677865521591610480503421)
  ·
    refine ⟨51629199570596853930188783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137677865521591610480503421 51629199570596853930188783)
    ·
      refine ⟨77443799355895280895283175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51629199570596853930188783 77443799355895280895283175)
      ·
        refine ⟨116165699033842921342924763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77443799355895280895283175 116165699033842921342924763)
        ·
          refine ⟨174248548550764382014387145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116165699033842921342924763 174248548550764382014387145)
          ·
            refine ⟨130686411413073286510790359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174248548550764382014387145 130686411413073286510790359)
            ·
              refine ⟨196029617119609929766185539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130686411413073286510790359 196029617119609929766185539)
              ·
                refine ⟨294044425679414894649278309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196029617119609929766185539 294044425679414894649278309)
                ·
                  refine ⟨55133329814890292746739683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 294044425679414894649278309 55133329814890292746739683)
                  ·
                    refine ⟨82699994722335439120109525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55133329814890292746739683 82699994722335439120109525)
                    ·
                      refine ⟨1938281126304736854377567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 82699994722335439120109525 1938281126304736854377567)
                      ·
                        rfl

theorem cell23_3774789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_3774789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774789 prefixEnd_3774789 := by exact prefixLift 3774789
  have htrace : WordTrace (prefixWord ++ tailWord_3774789) baseStart_3774789 baseEnd_3774789 := by
    simpa [prefixWord, tailWord_3774789, baseEnd_3774789] using wordTrace_append hprefix tailTrace_3774789
  have hstable : (prefixWord ++ tailWord_3774789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774789).length < 2 ^ (prefixWord ++ tailWord_3774789).sum := by decide
  have hdescent : baseEnd_3774789 < baseStart_3774789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774796 : List Nat := [2, 2, 1, 3, 2, 1, 2, 2, 3, 5]
def baseStart_3774796 : Nat := 118140960795 + 3774796 * 2 ^ 59
def prefixEnd_3774796 : Nat := 4983230072969 + 3 ^ 40 * 3774796 * 2
def baseEnd_3774796 : Nat := 646094906889772775663345

theorem tailTrace_3774796 : CollatzResearch.WordTrace tailWord_3774796 prefixEnd_3774796 646094906889772775663345 := by
  unfold tailWord_3774796
  simp only [CollatzResearch.WordTrace]
  refine ⟨68839060416283125338004121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91785413888377500450672161 68839060416283125338004121)
  ·
    refine ⟨51629295312212344003503091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68839060416283125338004121 51629295312212344003503091)
    ·
      refine ⟨77443942968318516005254637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51629295312212344003503091 77443942968318516005254637)
      ·
        refine ⟨29041478613119443501970489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77443942968318516005254637 29041478613119443501970489)
        ·
          refine ⟨21781108959839582626477867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29041478613119443501970489 21781108959839582626477867)
          ·
            refine ⟨32671663439759373939716801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21781108959839582626477867 32671663439759373939716801)
            ·
              refine ⟨24503747579819530454787601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32671663439759373939716801 24503747579819530454787601)
              ·
                refine ⟨18377810684864647841090701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24503747579819530454787601 18377810684864647841090701)
                ·
                  refine ⟨6891679006824242940409013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18377810684864647841090701 6891679006824242940409013)
                  ·
                    refine ⟨646094906889772775663345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6891679006824242940409013 646094906889772775663345)
                    ·
                      rfl

theorem cell23_3774796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 3, 5].length) (baseStart_3774796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774796 prefixEnd_3774796 := by exact prefixLift 3774796
  have htrace : WordTrace (prefixWord ++ tailWord_3774796) baseStart_3774796 baseEnd_3774796 := by
    simpa [prefixWord, tailWord_3774796, baseEnd_3774796] using wordTrace_append hprefix tailTrace_3774796
  have hstable : (prefixWord ++ tailWord_3774796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774796).length < 2 ^ (prefixWord ++ tailWord_3774796).sum := by decide
  have hdescent : baseEnd_3774796 < baseStart_3774796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774820 : List Nat := [2, 3, 1, 1, 3, 1, 4, 1, 2, 3, 2]
def baseStart_3774820 : Nat := 118140960795 + 3774820 * 2 ^ 59
def prefixEnd_3774820 : Nat := 4983230072969 + 3 ^ 40 * 3774820 * 2
def baseEnd_3774820 : Nat := 1938297044205026233089925

theorem tailTrace_3774820 : CollatzResearch.WordTrace tailWord_3774820 prefixEnd_3774820 1938297044205026233089925 := by
  unfold tailWord_3774820
  simp only [CollatzResearch.WordTrace]
  refine ⟨68839498092239651387440957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91785997456319535183254609 68839498092239651387440957)
  ·
    refine ⟨25814811784589869270290359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68839498092239651387440957 25814811784589869270290359)
    ·
      refine ⟨38722217676884803905435539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25814811784589869270290359 38722217676884803905435539)
      ·
        refine ⟨58083326515327205858153309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38722217676884803905435539 58083326515327205858153309)
        ·
          refine ⟨21781247443247702196807491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58083326515327205858153309 21781247443247702196807491)
          ·
            refine ⟨32671871164871553295211237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21781247443247702196807491 32671871164871553295211237)
            ·
              refine ⟨6125975843413416242852107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32671871164871553295211237 6125975843413416242852107)
              ·
                refine ⟨9188963765120124364278161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6125975843413416242852107 9188963765120124364278161)
                ·
                  refine ⟨6891722823840093273208621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9188963765120124364278161 6891722823840093273208621)
                  ·
                    refine ⟨2584396058940034977453233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6891722823840093273208621 2584396058940034977453233)
                    ·
                      refine ⟨1938297044205026233089925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2584396058940034977453233 1938297044205026233089925)
                      ·
                        rfl

theorem cell23_3774820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 2, 3, 2].length) (baseStart_3774820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774820 prefixEnd_3774820 := by exact prefixLift 3774820
  have htrace : WordTrace (prefixWord ++ tailWord_3774820) baseStart_3774820 baseEnd_3774820 := by
    simpa [prefixWord, tailWord_3774820, baseEnd_3774820] using wordTrace_append hprefix tailTrace_3774820
  have hstable : (prefixWord ++ tailWord_3774820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774820).length < 2 ^ (prefixWord ++ tailWord_3774820).sum := by decide
  have hdescent : baseEnd_3774820 < baseStart_3774820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774838 : List Nat := [5, 1, 1, 4, 2, 1, 2, 2, 1, 4]
def baseStart_3774838 : Nat := 118140960795 + 3774838 * 2 ^ 59
def prefixEnd_3774838 : Nat := 4983230072969 + 3 ^ 40 * 3774838 * 2
def baseEnd_3774838 : Nat := 646102095618935720888281

theorem tailTrace_3774838 : CollatzResearch.WordTrace tailWord_3774838 prefixEnd_3774838 646102095618935720888281 := by
  unfold tailWord_3774838
  simp only [CollatzResearch.WordTrace]
  refine ⟨8604978293650880740564823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91786435132276061232691445 8604978293650880740564823)
  ·
    refine ⟨12907467440476321110847235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8604978293650880740564823 12907467440476321110847235)
    ·
      refine ⟨19361201160714481666270853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12907467440476321110847235 19361201160714481666270853)
      ·
        refine ⟨3630225217633965312425785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19361201160714481666270853 3630225217633965312425785)
        ·
          refine ⟨2722668913225473984319339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3630225217633965312425785 2722668913225473984319339)
          ·
            refine ⟨4084003369838210976479009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2722668913225473984319339 4084003369838210976479009)
            ·
              refine ⟨3063002527378658232359257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4084003369838210976479009 3063002527378658232359257)
              ·
                refine ⟨2297251895533993674269443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3063002527378658232359257 2297251895533993674269443)
                ·
                  refine ⟨3445877843300990511404165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2297251895533993674269443 3445877843300990511404165)
                  ·
                    refine ⟨646102095618935720888281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3445877843300990511404165 646102095618935720888281)
                    ·
                      rfl

theorem cell23_3774838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_3774838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774838 prefixEnd_3774838 := by exact prefixLift 3774838
  have htrace : WordTrace (prefixWord ++ tailWord_3774838) baseStart_3774838 baseEnd_3774838 := by
    simpa [prefixWord, tailWord_3774838, baseEnd_3774838] using wordTrace_append hprefix tailTrace_3774838
  have hstable : (prefixWord ++ tailWord_3774838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774838).length < 2 ^ (prefixWord ++ tailWord_3774838).sum := by decide
  have hdescent : baseEnd_3774838 < baseStart_3774838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774843 : List Nat := [1, 1, 1, 1, 1, 7, 1, 4, 2, 4]
def baseStart_3774843 : Nat := 118140960795 + 3774843 * 2 ^ 59
def prefixEnd_3774843 : Nat := 4983230072969 + 3 ^ 40 * 3774843 * 2
def baseEnd_3774843 : Nat := 646102951420026547700773

theorem tailTrace_3774843 : CollatzResearch.WordTrace tailWord_3774843 prefixEnd_3774843 646102951420026547700773 := by
  unfold tailWord_3774843
  simp only [CollatzResearch.WordTrace]
  refine ⟨137679835063395977702969183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91786556708930651801979455 137679835063395977702969183)
  ·
    refine ⟨206519752595093966554453775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137679835063395977702969183 206519752595093966554453775)
    ·
      refine ⟨309779628892640949831680663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206519752595093966554453775 309779628892640949831680663)
      ·
        refine ⟨464669443338961424747520995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309779628892640949831680663 464669443338961424747520995)
        ·
          refine ⟨697004165008442137121281493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464669443338961424747520995 697004165008442137121281493)
          ·
            refine ⟨16336035117385362588780035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 697004165008442137121281493 16336035117385362588780035)
            ·
              refine ⟨24504052676078043883170053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16336035117385362588780035 24504052676078043883170053)
              ·
                refine ⟨4594509876764633228094385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24504052676078043883170053 4594509876764633228094385)
                ·
                  refine ⟨3445882407573474921070789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4594509876764633228094385 3445882407573474921070789)
                  ·
                    refine ⟨646102951420026547700773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3445882407573474921070789 646102951420026547700773)
                    ·
                      rfl

theorem cell23_3774843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 2, 4].length) (baseStart_3774843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774843 prefixEnd_3774843 := by exact prefixLift 3774843
  have htrace : WordTrace (prefixWord ++ tailWord_3774843) baseStart_3774843 baseEnd_3774843 := by
    simpa [prefixWord, tailWord_3774843, baseEnd_3774843] using wordTrace_append hprefix tailTrace_3774843
  have hstable : (prefixWord ++ tailWord_3774843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774843).length < 2 ^ (prefixWord ++ tailWord_3774843).sum := by decide
  have hdescent : baseEnd_3774843 < baseStart_3774843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774883 : List Nat := [1, 1, 1, 4, 1, 4, 2, 2, 1, 3, 3]
def baseStart_3774883 : Nat := 118140960795 + 3774883 * 2 ^ 59
def prefixEnd_3774883 : Nat := 4983230072969 + 3 ^ 40 * 3774883 * 2
def baseEnd_3774883 : Nat := 1938329393486259486602135

theorem tailTrace_3774883 : CollatzResearch.WordTrace tailWord_3774883 prefixEnd_3774883 1938329393486259486602135 := by
  unfold tailWord_3774883
  simp only [CollatzResearch.WordTrace]
  refine ⟨137681293983251064534425303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91787529322167376356283535 137681293983251064534425303)
  ·
    refine ⟨206521940974876596801637955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137681293983251064534425303 206521940974876596801637955)
    ·
      refine ⟨309782911462314895202456933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206521940974876596801637955 309782911462314895202456933)
      ·
        refine ⟨58084295899184042850460675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 309782911462314895202456933 58084295899184042850460675)
        ·
          refine ⟨87126443848776064275691013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58084295899184042850460675 87126443848776064275691013)
          ·
            refine ⟨16336208221645512051692065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87126443848776064275691013 16336208221645512051692065)
            ·
              refine ⟨12252156166234134038769049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16336208221645512051692065 12252156166234134038769049)
              ·
                refine ⟨9189117124675600529076787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12252156166234134038769049 9189117124675600529076787)
                ·
                  refine ⟨13783675687013400793615181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9189117124675600529076787 13783675687013400793615181)
                  ·
                    refine ⟨5168878382630025297605693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13783675687013400793615181 5168878382630025297605693)
                    ·
                      refine ⟨1938329393486259486602135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5168878382630025297605693 1938329393486259486602135)
                      ·
                        rfl

theorem cell23_3774883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_3774883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774883 prefixEnd_3774883 := by exact prefixLift 3774883
  have htrace : WordTrace (prefixWord ++ tailWord_3774883) baseStart_3774883 baseEnd_3774883 := by
    simpa [prefixWord, tailWord_3774883, baseEnd_3774883] using wordTrace_append hprefix tailTrace_3774883
  have hstable : (prefixWord ++ tailWord_3774883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774883).length < 2 ^ (prefixWord ++ tailWord_3774883).sum := by decide
  have hdescent : baseEnd_3774883 < baseStart_3774883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774887 : List Nat := [1, 1, 6, 1, 1, 2, 4, 1, 1, 2, 3]
def baseStart_3774887 : Nat := 118140960795 + 3774887 * 2 ^ 59
def prefixEnd_3774887 : Nat := 4983230072969 + 3 ^ 40 * 3774887 * 2
def baseEnd_3774887 : Nat := 1938331447408877470952117

theorem tailTrace_3774887 : CollatzResearch.WordTrace tailWord_3774887 prefixEnd_3774887 1938331447408877470952117 := by
  unfold tailWord_3774887
  simp only [CollatzResearch.WordTrace]
  refine ⟨137681439875236573217570915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91787626583491048811713943 137681439875236573217570915)
  ·
    refine ⟨206522159812854859826356373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137681439875236573217570915 206522159812854859826356373)
    ·
      refine ⟨9680726241227571554360455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 206522159812854859826356373 9680726241227571554360455)
      ·
        refine ⟨14521089361841357331540683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9680726241227571554360455 14521089361841357331540683)
        ·
          refine ⟨21781634042762035997311025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14521089361841357331540683 21781634042762035997311025)
          ·
            refine ⟨16336225532071526997983269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21781634042762035997311025 16336225532071526997983269)
            ·
              refine ⟨3063042287263411312121863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16336225532071526997983269 3063042287263411312121863)
              ·
                refine ⟨4594563430895116968182795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3063042287263411312121863 4594563430895116968182795)
                ·
                  refine ⟨6891845146342675452274193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4594563430895116968182795 6891845146342675452274193)
                  ·
                    refine ⟨5168883859757006589205645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6891845146342675452274193 5168883859757006589205645)
                    ·
                      refine ⟨1938331447408877470952117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5168883859757006589205645 1938331447408877470952117)
                      ·
                        rfl

theorem cell23_3774887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_3774887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774887 prefixEnd_3774887 := by exact prefixLift 3774887
  have htrace : WordTrace (prefixWord ++ tailWord_3774887) baseStart_3774887 baseEnd_3774887 := by
    simpa [prefixWord, tailWord_3774887, baseEnd_3774887] using wordTrace_append hprefix tailTrace_3774887
  have hstable : (prefixWord ++ tailWord_3774887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774887).length < 2 ^ (prefixWord ++ tailWord_3774887).sum := by decide
  have hdescent : baseEnd_3774887 < baseStart_3774887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774906 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 1, 5, 4]
def baseStart_3774906 : Nat := 118140960795 + 3774906 * 2 ^ 59
def prefixEnd_3774906 : Nat := 4983230072969 + 3 ^ 40 * 3774906 * 2
def baseEnd_3774906 : Nat := 1938341203541312896614529

theorem tailTrace_3774906 : CollatzResearch.WordTrace tailWord_3774906 prefixEnd_3774906 1938341203541312896614529 := by
  unfold tailWord_3774906
  simp only [CollatzResearch.WordTrace]
  refine ⟨34420533215541934865628143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91788088574778492975008381 34420533215541934865628143)
  ·
    refine ⟨51630799823312902298442215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34420533215541934865628143 51630799823312902298442215)
    ·
      refine ⟨77446199734969353447663323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51630799823312902298442215 77446199734969353447663323)
      ·
        refine ⟨116169299602454030171494985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77446199734969353447663323 116169299602454030171494985)
        ·
          refine ⟨87126974701840522628621239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116169299602454030171494985 87126974701840522628621239)
          ·
            refine ⟨130690462052760783942931859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87126974701840522628621239 130690462052760783942931859)
            ·
              refine ⟨196035693079141175914397789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130690462052760783942931859 196035693079141175914397789)
              ·
                refine ⟨73513384904677940967899171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196035693079141175914397789 73513384904677940967899171)
                ·
                  refine ⟨110270077357016911451848757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73513384904677940967899171 110270077357016911451848757)
                  ·
                    refine ⟨10337819752220335448610821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 110270077357016911451848757 10337819752220335448610821)
                    ·
                      refine ⟨1938341203541312896614529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10337819752220335448610821 1938341203541312896614529)
                      ·
                        rfl

theorem cell23_3774906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_3774906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774906 prefixEnd_3774906 := by exact prefixLift 3774906
  have htrace : WordTrace (prefixWord ++ tailWord_3774906) baseStart_3774906 baseEnd_3774906 := by
    simpa [prefixWord, tailWord_3774906, baseEnd_3774906] using wordTrace_append hprefix tailTrace_3774906
  have hstable : (prefixWord ++ tailWord_3774906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774906).length < 2 ^ (prefixWord ++ tailWord_3774906).sum := by decide
  have hdescent : baseEnd_3774906 < baseStart_3774906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774910 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2]
def baseStart_3774910 : Nat := 118140960795 + 3774910 * 2 ^ 59
def prefixEnd_3774910 : Nat := 4983230072969 + 3 ^ 40 * 3774910 * 2
def baseEnd_3774910 : Nat := 1938343257463930880964511

theorem tailTrace_3774910 : CollatzResearch.WordTrace tailWord_3774910 prefixEnd_3774910 1938343257463930880964511 := by
  unfold tailWord_3774910
  simp only [CollatzResearch.WordTrace]
  refine ⟨17210284844269156018207273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91788185836102165430438789 17210284844269156018207273)
  ·
    refine ⟨12907713633201867013655455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17210284844269156018207273 12907713633201867013655455)
    ·
      refine ⟨19361570449802800520483183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12907713633201867013655455 19361570449802800520483183)
      ·
        refine ⟨29042355674704200780724775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19361570449802800520483183 29042355674704200780724775)
        ·
          refine ⟨43563533512056301171087163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29042355674704200780724775 43563533512056301171087163)
          ·
            refine ⟨65345300268084451756630745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43563533512056301171087163 65345300268084451756630745)
            ·
              refine ⟨49008975201063338817473059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65345300268084451756630745 49008975201063338817473059)
              ·
                refine ⟨73513462801595008226209589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49008975201063338817473059 73513462801595008226209589)
                ·
                  refine ⟨6891887137649532021207149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73513462801595008226209589 6891887137649532021207149)
                  ·
                    refine ⟨2584457676618574507952681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6891887137649532021207149 2584457676618574507952681)
                    ·
                      refine ⟨1938343257463930880964511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2584457676618574507952681 1938343257463930880964511)
                      ·
                        rfl

theorem cell23_3774910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_3774910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774910 prefixEnd_3774910 := by exact prefixLift 3774910
  have htrace : WordTrace (prefixWord ++ tailWord_3774910) baseStart_3774910 baseEnd_3774910 := by
    simpa [prefixWord, tailWord_3774910, baseEnd_3774910] using wordTrace_append hprefix tailTrace_3774910
  have hstable : (prefixWord ++ tailWord_3774910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774910).length < 2 ^ (prefixWord ++ tailWord_3774910).sum := by decide
  have hdescent : baseEnd_3774910 < baseStart_3774910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774943 : List Nat := [1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 5]
def baseStart_3774943 : Nat := 118140960795 + 3774943 * 2 ^ 59
def prefixEnd_3774943 : Nat := 4983230072969 + 3 ^ 40 * 3774943 * 2
def baseEnd_3774943 : Nat := 1938360202325529251851859

theorem tailTrace_3774943 : CollatzResearch.WordTrace tailWord_3774943 prefixEnd_3774943 1938360202325529251851859 := by
  unfold tailWord_3774943
  simp only [CollatzResearch.WordTrace]
  refine ⟨137683482363033694781609483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91788988242022463187739655 137683482363033694781609483)
  ·
    refine ⟨206525223544550542172414225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137683482363033694781609483 206525223544550542172414225)
    ·
      refine ⟨154893917658412906629310669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206525223544550542172414225 154893917658412906629310669)
      ·
        refine ⟨58085219121904839985991501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154893917658412906629310669 58085219121904839985991501)
        ·
          refine ⟨21781957170714314994746813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58085219121904839985991501 21781957170714314994746813)
          ·
            refine ⟨8168233939017868123030055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21781957170714314994746813 8168233939017868123030055)
            ·
              refine ⟨12252350908526802184545083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8168233939017868123030055 12252350908526802184545083)
              ·
                refine ⟨18378526362790203276817625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12252350908526802184545083 18378526362790203276817625)
                ·
                  refine ⟨13783894772092652457613219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18378526362790203276817625 13783894772092652457613219)
                  ·
                    refine ⟨20675842158138978686419829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13783894772092652457613219 20675842158138978686419829)
                    ·
                      refine ⟨1938360202325529251851859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20675842158138978686419829 1938360202325529251851859)
                      ·
                        rfl

theorem cell23_3774943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_3774943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774943 prefixEnd_3774943 := by exact prefixLift 3774943
  have htrace : WordTrace (prefixWord ++ tailWord_3774943) baseStart_3774943 baseEnd_3774943 := by
    simpa [prefixWord, tailWord_3774943, baseEnd_3774943] using wordTrace_append hprefix tailTrace_3774943
  have hstable : (prefixWord ++ tailWord_3774943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774943).length < 2 ^ (prefixWord ++ tailWord_3774943).sum := by decide
  have hdescent : baseEnd_3774943 < baseStart_3774943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774956 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 7]
def baseStart_3774956 : Nat := 118140960795 + 3774956 * 2 ^ 59
def prefixEnd_3774956 : Nat := 4983230072969 + 3 ^ 40 * 3774956 * 2
def baseEnd_3774956 : Nat := 1938366877574037700989299

theorem tailTrace_3774956 : CollatzResearch.WordTrace tailWord_3774956 prefixEnd_3774956 1938366877574037700989299 := by
  unfold tailWord_3774956
  simp only [CollatzResearch.WordTrace]
  refine ⟨68841978255993299000916361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91789304341324398667888481 68841978255993299000916361)
  ·
    refine ⟨51631483691994974250687271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68841978255993299000916361 51631483691994974250687271)
    ·
      refine ⟨77447225537992461376030907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51631483691994974250687271 77447225537992461376030907)
      ·
        refine ⟨116170838306988692064046361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77447225537992461376030907 116170838306988692064046361)
        ·
          refine ⟨87128128730241519048034771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116170838306988692064046361 87128128730241519048034771)
          ·
            refine ⟨130692193095362278572052157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87128128730241519048034771 130692193095362278572052157)
            ·
              refine ⟨49009572410760854464519559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130692193095362278572052157 49009572410760854464519559)
              ·
                refine ⟨73514358616141281696779339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49009572410760854464519559 73514358616141281696779339)
                ·
                  refine ⟨110271537924211922545169009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73514358616141281696779339 110271537924211922545169009)
                  ·
                    refine ⟨82703653443158941908876757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 110271537924211922545169009 82703653443158941908876757)
                    ·
                      refine ⟨1938366877574037700989299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 82703653443158941908876757 1938366877574037700989299)
                      ·
                        rfl

theorem cell23_3774956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_3774956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774956 prefixEnd_3774956 := by exact prefixLift 3774956
  have htrace : WordTrace (prefixWord ++ tailWord_3774956) baseStart_3774956 baseEnd_3774956 := by
    simpa [prefixWord, tailWord_3774956, baseEnd_3774956] using wordTrace_append hprefix tailTrace_3774956
  have hstable : (prefixWord ++ tailWord_3774956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774956).length < 2 ^ (prefixWord ++ tailWord_3774956).sum := by decide
  have hdescent : baseEnd_3774956 < baseStart_3774956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774973 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 1, 5, 3]
def baseStart_3774973 : Nat := 118140960795 + 3774973 * 2 ^ 59
def prefixEnd_3774973 : Nat := 4983230072969 + 3 ^ 40 * 3774973 * 2
def baseEnd_3774973 : Nat := 1938375606745164134476721

theorem tailTrace_3774973 : CollatzResearch.WordTrace tailWord_3774973 prefixEnd_3774973 1938375606745164134476721 := by
  unfold tailWord_3774973
  simp only [CollatzResearch.WordTrace]
  refine ⟨137684576552925009905201573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91789717701950006603467715 137684576552925009905201573)
  ·
    refine ⟨25815858103673439357225295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137684576552925009905201573 25815858103673439357225295)
    ·
      refine ⟨38723787155510159035837943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25815858103673439357225295 38723787155510159035837943)
      ·
        refine ⟨58085680733265238553756915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38723787155510159035837943 58085680733265238553756915)
        ·
          refine ⟨87128521099897857830635373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58085680733265238553756915 87128521099897857830635373)
          ·
            refine ⟨32673195412461696686488265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87128521099897857830635373 32673195412461696686488265)
            ·
              refine ⟨24504896559346272514866199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32673195412461696686488265 24504896559346272514866199)
              ·
                refine ⟨36757344839019408772299299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24504896559346272514866199 36757344839019408772299299)
                ·
                  refine ⟨55136017258529113158448949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36757344839019408772299299 55136017258529113158448949)
                  ·
                    refine ⟨5169001617987104358604589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55136017258529113158448949 5169001617987104358604589)
                    ·
                      refine ⟨1938375606745164134476721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5169001617987104358604589 1938375606745164134476721)
                      ·
                        rfl

theorem cell23_3774973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_3774973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774973 prefixEnd_3774973 := by exact prefixLift 3774973
  have htrace : WordTrace (prefixWord ++ tailWord_3774973) baseStart_3774973 baseEnd_3774973 := by
    simpa [prefixWord, tailWord_3774973, baseEnd_3774973] using wordTrace_append hprefix tailTrace_3774973
  have hstable : (prefixWord ++ tailWord_3774973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774973).length < 2 ^ (prefixWord ++ tailWord_3774973).sum := by decide
  have hdescent : baseEnd_3774973 < baseStart_3774973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3774978 : List Nat := [3, 4, 1, 2, 3, 1, 1, 2, 1, 3, 2]
def baseStart_3774978 : Nat := 118140960795 + 3774978 * 2 ^ 59
def prefixEnd_3774978 : Nat := 4983230072969 + 3 ^ 40 * 3774978 * 2
def baseEnd_3774978 : Nat := 1938378174148436614914199

theorem tailTrace_3774978 : CollatzResearch.WordTrace tailWord_3774978 prefixEnd_3774978 1938378174148436614914199 := by
  unfold tailWord_3774978
  simp only [CollatzResearch.WordTrace]
  refine ⟨34421189729476723939783397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91789839278604597172755725 34421189729476723939783397)
  ·
    refine ⟨6453973074276885738709387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34421189729476723939783397 6453973074276885738709387)
    ·
      refine ⟨9680959611415328608064081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6453973074276885738709387 9680959611415328608064081)
      ·
        refine ⟨7260719708561496456048061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9680959611415328608064081 7260719708561496456048061)
        ·
          refine ⟨2722769890710561171018023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7260719708561496456048061 2722769890710561171018023)
          ·
            refine ⟨4084154836065841756527035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2722769890710561171018023 4084154836065841756527035)
            ·
              refine ⟨6126232254098762634790553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4084154836065841756527035 6126232254098762634790553)
              ·
                refine ⟨4594674190574071976092915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6126232254098762634790553 4594674190574071976092915)
                ·
                  refine ⟨6892011285861107964139373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4594674190574071976092915 6892011285861107964139373)
                  ·
                    refine ⟨2584504232197915486552265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6892011285861107964139373 2584504232197915486552265)
                    ·
                      refine ⟨1938378174148436614914199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2584504232197915486552265 1938378174148436614914199)
                      ·
                        rfl

theorem cell23_3774978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_3774978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3774978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3774978 prefixEnd_3774978 := by exact prefixLift 3774978
  have htrace : WordTrace (prefixWord ++ tailWord_3774978) baseStart_3774978 baseEnd_3774978 := by
    simpa [prefixWord, tailWord_3774978, baseEnd_3774978] using wordTrace_append hprefix tailTrace_3774978
  have hstable : (prefixWord ++ tailWord_3774978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3774978).length < 2 ^ (prefixWord ++ tailWord_3774978).sum := by decide
  have hdescent : baseEnd_3774978 < baseStart_3774978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3774978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775023 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 9, 4]
def baseStart_3775023 : Nat := 118140960795 + 3775023 * 2 ^ 59
def prefixEnd_3775023 : Nat := 4983230072969 + 3 ^ 40 * 3775023 * 2
def baseEnd_3775023 : Nat := 646133760259296312950497

theorem tailTrace_3775023 : CollatzResearch.WordTrace tailWord_3775023 prefixEnd_3775023 646133760259296312950497 := by
  unfold tailWord_3775023
  simp only [CollatzResearch.WordTrace]
  refine ⟨137686400202743868444521723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91790933468495912296347815 137686400202743868444521723)
  ·
    refine ⟨206529600304115802666782585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137686400202743868444521723 206529600304115802666782585)
    ·
      refine ⟨154897200228086852000086939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206529600304115802666782585 154897200228086852000086939)
      ·
        refine ⟨232345800342130278000130409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154897200228086852000086939 232345800342130278000130409)
        ·
          refine ⟨174259350256597708500097807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232345800342130278000130409 174259350256597708500097807)
          ·
            refine ⟨261389025384896562750146711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174259350256597708500097807 261389025384896562750146711)
            ·
              refine ⟨392083538077344844125220067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261389025384896562750146711 392083538077344844125220067)
              ·
                refine ⟨588125307116017266187830101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 392083538077344844125220067 588125307116017266187830101)
                ·
                  refine ⟨3446046721382913669069317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 588125307116017266187830101 3446046721382913669069317)
                  ·
                    refine ⟨646133760259296312950497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3446046721382913669069317 646133760259296312950497)
                    ·
                      rfl

theorem cell23_3775023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 9, 4].length) (baseStart_3775023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775023 prefixEnd_3775023 := by exact prefixLift 3775023
  have htrace : WordTrace (prefixWord ++ tailWord_3775023) baseStart_3775023 baseEnd_3775023 := by
    simpa [prefixWord, tailWord_3775023, baseEnd_3775023] using wordTrace_append hprefix tailTrace_3775023
  have hstable : (prefixWord ++ tailWord_3775023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775023).length < 2 ^ (prefixWord ++ tailWord_3775023).sum := by decide
  have hdescent : baseEnd_3775023 < baseStart_3775023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775044 : List Nat := [2, 3, 5, 1, 1, 1, 1, 1, 1, 7]
def baseStart_3775044 : Nat := 118140960795 + 3775044 * 2 ^ 59
def prefixEnd_3775044 : Nat := 4983230072969 + 3 ^ 40 * 3775044 * 2
def baseEnd_3775044 : Nat := 646137354623877785562965

theorem tailTrace_3775044 : CollatzResearch.WordTrace tailWord_3775044 prefixEnd_3775044 646137354623877785562965 := by
  unfold tailWord_3775044
  simp only [CollatzResearch.WordTrace]
  refine ⟨68843583067833894515518093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91791444090445192687357457 68843583067833894515518093)
  ·
    refine ⟨25816343650437710443319285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68843583067833894515518093 25816343650437710443319285)
    ·
      refine ⟨2420282217228535354061183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25816343650437710443319285 2420282217228535354061183)
      ·
        refine ⟨3630423325842803031091775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2420282217228535354061183 3630423325842803031091775)
        ·
          refine ⟨5445634988764204546637663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3630423325842803031091775 5445634988764204546637663)
          ·
            refine ⟨8168452483146306819956495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5445634988764204546637663 8168452483146306819956495)
            ·
              refine ⟨12252678724719460229934743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8168452483146306819956495 12252678724719460229934743)
              ·
                refine ⟨18379018087079190344902115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12252678724719460229934743 18379018087079190344902115)
                ·
                  refine ⟨27568527130618785517353173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18379018087079190344902115 27568527130618785517353173)
                  ·
                    refine ⟨646137354623877785562965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27568527130618785517353173 646137354623877785562965)
                    ·
                      rfl

theorem cell23_3775044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_3775044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775044 prefixEnd_3775044 := by exact prefixLift 3775044
  have htrace : WordTrace (prefixWord ++ tailWord_3775044) baseStart_3775044 baseEnd_3775044 := by
    simpa [prefixWord, tailWord_3775044, baseEnd_3775044] using wordTrace_append hprefix tailTrace_3775044
  have hstable : (prefixWord ++ tailWord_3775044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775044).length < 2 ^ (prefixWord ++ tailWord_3775044).sum := by decide
  have hdescent : baseEnd_3775044 < baseStart_3775044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775047 : List Nat := [1, 1, 4, 1, 4, 3, 1, 1, 2, 1, 4]
def baseStart_3775047 : Nat := 118140960795 + 3775047 * 2 ^ 59
def prefixEnd_3775047 : Nat := 4983230072969 + 3 ^ 40 * 3775047 * 2
def baseEnd_3775047 : Nat := 1938413604313596844951381

theorem tailTrace_3775047 : CollatzResearch.WordTrace tailWord_3775047 prefixEnd_3775047 1938413604313596844951381 := by
  unfold tailWord_3775047
  simp only [CollatzResearch.WordTrace]
  refine ⟨137687275554656920543395395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91791517036437947028930263 137687275554656920543395395)
  ·
    refine ⟨206530913331985380815093093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137687275554656920543395395 206530913331985380815093093)
    ·
      refine ⟨38724546249747258902829955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206530913331985380815093093 38724546249747258902829955)
      ·
        refine ⟨58086819374620888354244933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38724546249747258902829955 58086819374620888354244933)
        ·
          refine ⟨10891278632741416566420925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58086819374620888354244933 10891278632741416566420925)
          ·
            refine ⟨4084229487278031212407847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10891278632741416566420925 4084229487278031212407847)
            ·
              refine ⟨6126344230917046818611771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4084229487278031212407847 6126344230917046818611771)
              ·
                refine ⟨9189516346375570227917657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6126344230917046818611771 9189516346375570227917657)
                ·
                  refine ⟨6892137259781677670938243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9189516346375570227917657 6892137259781677670938243)
                  ·
                    refine ⟨10338205889672516506407365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6892137259781677670938243 10338205889672516506407365)
                    ·
                      refine ⟨1938413604313596844951381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10338205889672516506407365 1938413604313596844951381)
                      ·
                        rfl

theorem cell23_3775047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_3775047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775047 prefixEnd_3775047 := by exact prefixLift 3775047
  have htrace : WordTrace (prefixWord ++ tailWord_3775047) baseStart_3775047 baseEnd_3775047 := by
    simpa [prefixWord, tailWord_3775047, baseEnd_3775047] using wordTrace_append hprefix tailTrace_3775047
  have hstable : (prefixWord ++ tailWord_3775047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775047).length < 2 ^ (prefixWord ++ tailWord_3775047).sum := by decide
  have hdescent : baseEnd_3775047 < baseStart_3775047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775050 : List Nat := [3, 1, 2, 1, 1, 5, 1, 1, 1, 4, 3]
def baseStart_3775050 : Nat := 118140960795 + 3775050 * 2 ^ 59
def prefixEnd_3775050 : Nat := 4983230072969 + 3 ^ 40 * 3775050 * 2
def baseEnd_3775050 : Nat := 1938415144755560333213867

theorem tailTrace_3775050 : CollatzResearch.WordTrace tailWord_3775050 prefixEnd_3775050 1938415144755560333213867 := by
  unfold tailWord_3775050
  simp only [CollatzResearch.WordTrace]
  refine ⟨34421846243411513013938651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91791589982430701370503069 34421846243411513013938651)
  ·
    refine ⟨51632769365117269520907977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34421846243411513013938651 51632769365117269520907977)
    ·
      refine ⟨38724577023837952140680983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51632769365117269520907977 38724577023837952140680983)
      ·
        refine ⟨58086865535756928211021475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38724577023837952140680983 58086865535756928211021475)
        ·
          refine ⟨87130298303635392316532213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58086865535756928211021475 87130298303635392316532213)
          ·
            refine ⟨8168465465965818029674895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87130298303635392316532213 8168465465965818029674895)
            ·
              refine ⟨12252698198948727044512343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8168465465965818029674895 12252698198948727044512343)
              ·
                refine ⟨18379047298423090566768515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12252698198948727044512343 18379047298423090566768515)
                ·
                  refine ⟨27568570947634635850152773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18379047298423090566768515 27568570947634635850152773)
                  ·
                    refine ⟨5169107052681494221903645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27568570947634635850152773 5169107052681494221903645)
                    ·
                      refine ⟨1938415144755560333213867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5169107052681494221903645 1938415144755560333213867)
                      ·
                        rfl

theorem cell23_3775050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_3775050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775050 prefixEnd_3775050 := by exact prefixLift 3775050
  have htrace : WordTrace (prefixWord ++ tailWord_3775050) baseStart_3775050 baseEnd_3775050 := by
    simpa [prefixWord, tailWord_3775050, baseEnd_3775050] using wordTrace_append hprefix tailTrace_3775050
  have hstable : (prefixWord ++ tailWord_3775050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775050).length < 2 ^ (prefixWord ++ tailWord_3775050).sum := by decide
  have hdescent : baseEnd_3775050 < baseStart_3775050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775057 : List Nat := [1, 2, 2, 1, 3, 3, 1, 5, 1, 4]
def baseStart_3775057 : Nat := 118140960795 + 3775057 * 2 ^ 59
def prefixEnd_3775057 : Nat := 4983230072969 + 3 ^ 40 * 3775057 * 2
def baseEnd_3775057 : Nat := 646139579706713935275445

theorem tailTrace_3775057 : CollatzResearch.WordTrace tailWord_3775057 prefixEnd_3775057 646139579706713935275445 := by
  unfold tailWord_3775057
  simp only [CollatzResearch.WordTrace]
  refine ⟨137687640284620692251259425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91791760189747128167506283 137687640284620692251259425)
  ·
    refine ⟨103265730213465519188444569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137687640284620692251259425 103265730213465519188444569)
    ·
      refine ⟨77449297660099139391333427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103265730213465519188444569 77449297660099139391333427)
      ·
        refine ⟨116173946490148709087000141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77449297660099139391333427 116173946490148709087000141)
        ·
          refine ⟨43565229933805765907625053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116173946490148709087000141 43565229933805765907625053)
          ·
            refine ⟨16336961225177162215359395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43565229933805765907625053 16336961225177162215359395)
            ·
              refine ⟨24505441837765743323039093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16336961225177162215359395 24505441837765743323039093)
              ·
                refine ⟨2297385172290538436534915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24505441837765743323039093 2297385172290538436534915)
                ·
                  refine ⟨3446077758435807654802373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2297385172290538436534915 3446077758435807654802373)
                  ·
                    refine ⟨646139579706713935275445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3446077758435807654802373 646139579706713935275445)
                    ·
                      rfl

theorem cell23_3775057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 5, 1, 4].length) (baseStart_3775057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775057 prefixEnd_3775057 := by exact prefixLift 3775057
  have htrace : WordTrace (prefixWord ++ tailWord_3775057) baseStart_3775057 baseEnd_3775057 := by
    simpa [prefixWord, tailWord_3775057, baseEnd_3775057] using wordTrace_append hprefix tailTrace_3775057
  have hstable : (prefixWord ++ tailWord_3775057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775057).length < 2 ^ (prefixWord ++ tailWord_3775057).sum := by decide
  have hdescent : baseEnd_3775057 < baseStart_3775057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775073 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 1, 2, 6]
def baseStart_3775073 : Nat := 118140960795 + 3775073 * 2 ^ 59
def prefixEnd_3775073 : Nat := 4983230072969 + 3 ^ 40 * 3775073 * 2
def baseEnd_3775073 : Nat := 1938426954810613743226261

theorem tailTrace_3775073 : CollatzResearch.WordTrace tailWord_3775073 prefixEnd_3775073 1938426954810613743226261 := by
  unfold tailWord_3775073
  simp only [CollatzResearch.WordTrace]
  refine ⟨137688223852562726983841873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91792149235041817989227915 137688223852562726983841873)
  ·
    refine ⟨103266167889422045237881405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137688223852562726983841873 103266167889422045237881405)
    ·
      refine ⟨38724812958533266964205527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103266167889422045237881405 38724812958533266964205527)
      ·
        refine ⟨58087219437799900446308291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38724812958533266964205527 58087219437799900446308291)
        ·
          refine ⟨87130829156699850669462437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58087219437799900446308291 87130829156699850669462437)
          ·
            refine ⟨16337030466881222000524207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87130829156699850669462437 16337030466881222000524207)
            ·
              refine ⟨24505545700321833000786311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16337030466881222000524207 24505545700321833000786311)
              ·
                refine ⟨36758318550482749501179467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24505545700321833000786311 36758318550482749501179467)
                ·
                  refine ⟨55137477825724124251769201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36758318550482749501179467 55137477825724124251769201)
                  ·
                    refine ⟨41353108369293093188826901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55137477825724124251769201 41353108369293093188826901)
                    ·
                      refine ⟨1938426954810613743226261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41353108369293093188826901 1938426954810613743226261)
                      ·
                        rfl

theorem cell23_3775073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_3775073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775073 prefixEnd_3775073 := by exact prefixLift 3775073
  have htrace : WordTrace (prefixWord ++ tailWord_3775073) baseStart_3775073 baseEnd_3775073 := by
    simpa [prefixWord, tailWord_3775073, baseEnd_3775073] using wordTrace_append hprefix tailTrace_3775073
  have hstable : (prefixWord ++ tailWord_3775073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775073).length < 2 ^ (prefixWord ++ tailWord_3775073).sum := by decide
  have hdescent : baseEnd_3775073 < baseStart_3775073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775083 : List Nat := [1, 1, 1, 1, 2, 2, 1, 6, 3, 5]
def baseStart_3775083 : Nat := 118140960795 + 3775083 * 2 ^ 59
def prefixEnd_3775083 : Nat := 4983230072969 + 3 ^ 40 * 3775083 * 2
def baseEnd_3775083 : Nat := 646144029872386234700405

theorem tailTrace_3775083 : CollatzResearch.WordTrace tailWord_3775083 prefixEnd_3775083 646144029872386234700405 := by
  unfold tailWord_3775083
  simp only [CollatzResearch.WordTrace]
  refine ⟨137688588582526498691705903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91792392388350999127803935 137688588582526498691705903)
  ·
    refine ⟨206532882873789748037558855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137688588582526498691705903 206532882873789748037558855)
    ·
      refine ⟨309799324310684622056338283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206532882873789748037558855 309799324310684622056338283)
      ·
        refine ⟨464698986466026933084507425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309799324310684622056338283 464698986466026933084507425)
        ·
          refine ⟨348524239849520199813380569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464698986466026933084507425 348524239849520199813380569)
          ·
            refine ⟨261393179887140149860035427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348524239849520199813380569 261393179887140149860035427)
            ·
              refine ⟨392089769830710224790053141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261393179887140149860035427 392089769830710224790053141)
              ·
                refine ⟨18379207960814541787033741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 392089769830710224790053141 18379207960814541787033741)
                ·
                  refine ⟨6892202985305453170137653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18379207960814541787033741 6892202985305453170137653)
                  ·
                    refine ⟨646144029872386234700405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6892202985305453170137653 646144029872386234700405)
                    ·
                      rfl

theorem cell23_3775083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 5].length) (baseStart_3775083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775083 prefixEnd_3775083 := by exact prefixLift 3775083
  have htrace : WordTrace (prefixWord ++ tailWord_3775083) baseStart_3775083 baseEnd_3775083 := by
    simpa [prefixWord, tailWord_3775083, baseEnd_3775083] using wordTrace_append hprefix tailTrace_3775083
  have hstable : (prefixWord ++ tailWord_3775083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775083).length < 2 ^ (prefixWord ++ tailWord_3775083).sum := by decide
  have hdescent : baseEnd_3775083 < baseStart_3775083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775097 : List Nat := [1, 2, 1, 3, 3, 2, 2, 2, 3, 1, 3]
def baseStart_3775097 : Nat := 118140960795 + 3775097 * 2 ^ 59
def prefixEnd_3775097 : Nat := 4983230072969 + 3 ^ 40 * 3775097 * 2
def baseEnd_3775097 : Nat := 1938439278346321649326151

theorem tailTrace_3775097 : CollatzResearch.WordTrace tailWord_3775097 prefixEnd_3775097 1938439278346321649326151 := by
  unfold tailWord_3775097
  simp only [CollatzResearch.WordTrace]
  refine ⟨137689099204475779082715545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91792732802983852721810363 137689099204475779082715545)
  ·
    refine ⟨103266824403356834312036659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137689099204475779082715545 103266824403356834312036659)
    ·
      refine ⟨154900236605035251468054989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103266824403356834312036659 154900236605035251468054989)
      ·
        refine ⟨58087588726888219300520621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154900236605035251468054989 58087588726888219300520621)
        ·
          refine ⟨21782845772583082237695233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58087588726888219300520621 21782845772583082237695233)
          ·
            refine ⟨16337134329437311678271425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21782845772583082237695233 16337134329437311678271425)
            ·
              refine ⟨12252850747077983758703569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16337134329437311678271425 12252850747077983758703569)
              ·
                refine ⟨9189638060308487819027677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12252850747077983758703569 9189638060308487819027677)
                ·
                  refine ⟨3446114272615682932135379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9189638060308487819027677 3446114272615682932135379)
                  ·
                    refine ⟨5169171408923524398203069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3446114272615682932135379 5169171408923524398203069)
                    ·
                      refine ⟨1938439278346321649326151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5169171408923524398203069 1938439278346321649326151)
                      ·
                        rfl

theorem cell23_3775097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 3, 1, 3].length) (baseStart_3775097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775097 prefixEnd_3775097 := by exact prefixLift 3775097
  have htrace : WordTrace (prefixWord ++ tailWord_3775097) baseStart_3775097 baseEnd_3775097 := by
    simpa [prefixWord, tailWord_3775097, baseEnd_3775097] using wordTrace_append hprefix tailTrace_3775097
  have hstable : (prefixWord ++ tailWord_3775097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775097).length < 2 ^ (prefixWord ++ tailWord_3775097).sum := by decide
  have hdescent : baseEnd_3775097 < baseStart_3775097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775100 : List Nat := [2, 2, 2, 1, 1, 2, 3, 4, 1, 5]
def baseStart_3775100 : Nat := 118140960795 + 3775100 * 2 ^ 59
def prefixEnd_3775100 : Nat := 4983230072969 + 3 ^ 40 * 3775100 * 2
def baseEnd_3775100 : Nat := 646146939596095045862879

theorem tailTrace_3775100 : CollatzResearch.WordTrace tailWord_3775100 prefixEnd_3775100 646146939596095045862879 := by
  unfold tailWord_3775100
  simp only [CollatzResearch.WordTrace]
  refine ⟨68844604311732455297537377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91792805748976607063383169 68844604311732455297537377)
  ·
    refine ⟨51633453233799341473153033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68844604311732455297537377 51633453233799341473153033)
    ·
      refine ⟨38725089925349506104864775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51633453233799341473153033 38725089925349506104864775)
      ·
        refine ⟨58087634888024259157297163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38725089925349506104864775 58087634888024259157297163)
        ·
          refine ⟨87131452332036388735945745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58087634888024259157297163 87131452332036388735945745)
          ·
            refine ⟨65348589249027291551959309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87131452332036388735945745 65348589249027291551959309)
            ·
              refine ⟨24505720968385234331984741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65348589249027291551959309 24505720968385234331984741)
              ·
                refine ⟨4594822681572231437247139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24505720968385234331984741 4594822681572231437247139)
                ·
                  refine ⟨6892234022358347155870709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4594822681572231437247139 6892234022358347155870709)
                  ·
                    refine ⟨646146939596095045862879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6892234022358347155870709 646146939596095045862879)
                    ·
                      rfl

theorem cell23_3775100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_3775100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775100 prefixEnd_3775100 := by exact prefixLift 3775100
  have htrace : WordTrace (prefixWord ++ tailWord_3775100) baseStart_3775100 baseEnd_3775100 := by
    simpa [prefixWord, tailWord_3775100, baseEnd_3775100] using wordTrace_append hprefix tailTrace_3775100
  have hstable : (prefixWord ++ tailWord_3775100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775100).length < 2 ^ (prefixWord ++ tailWord_3775100).sum := by decide
  have hdescent : baseEnd_3775100 < baseStart_3775100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775113 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 3, 6]
def baseStart_3775113 : Nat := 118140960795 + 3775113 * 2 ^ 59
def prefixEnd_3775113 : Nat := 4983230072969 + 3 ^ 40 * 3775113 * 2
def baseEnd_3775113 : Nat := 646149164678931195575359

theorem tailTrace_3775113 : CollatzResearch.WordTrace tailWord_3775113 prefixEnd_3775113 646149164678931195575359 := by
  unfold tailWord_3775113
  simp only [CollatzResearch.WordTrace]
  refine ⟨137689682772417813815297993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91793121848278542543531995 137689682772417813815297993)
  ·
    refine ⟨103267262079313360361473495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137689682772417813815297993 103267262079313360361473495)
    ·
      refine ⟨154900893118970040542210243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103267262079313360361473495 154900893118970040542210243)
      ·
        refine ⟨232351339678455060813315365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154900893118970040542210243 232351339678455060813315365)
        ·
          refine ⟨43565876189710323902496631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 232351339678455060813315365 43565876189710323902496631)
          ·
            refine ⟨65348814284565485853744947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43565876189710323902496631 65348814284565485853744947)
            ·
              refine ⟨98023221426848228780617421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65348814284565485853744947 98023221426848228780617421)
              ·
                refine ⟨36758708035068085792731533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98023221426848228780617421 36758708035068085792731533)
                ·
                  refine ⟨13784515513150532172274325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36758708035068085792731533 13784515513150532172274325)
                  ·
                    refine ⟨646149164678931195575359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13784515513150532172274325 646149164678931195575359)
                    ·
                      rfl

theorem cell23_3775113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 6].length) (baseStart_3775113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775113 prefixEnd_3775113 := by exact prefixLift 3775113
  have htrace : WordTrace (prefixWord ++ tailWord_3775113) baseStart_3775113 baseEnd_3775113 := by
    simpa [prefixWord, tailWord_3775113, baseEnd_3775113] using wordTrace_append hprefix tailTrace_3775113
  have hstable : (prefixWord ++ tailWord_3775113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775113).length < 2 ^ (prefixWord ++ tailWord_3775113).sum := by decide
  have hdescent : baseEnd_3775113 < baseStart_3775113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775123 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 5]
def baseStart_3775123 : Nat := 118140960795 + 3775123 * 2 ^ 59
def prefixEnd_3775123 : Nat := 4983230072969 + 3 ^ 40 * 3775123 * 2
def baseEnd_3775123 : Nat := 1938452628843338547601031

theorem tailTrace_3775123 : CollatzResearch.WordTrace tailWord_3775123 prefixEnd_3775123 1938452628843338547601031 := by
  unfold tailWord_3775123
  simp only [CollatzResearch.WordTrace]
  refine ⟨137690047502381585523162023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91793365001587723682108015 137690047502381585523162023)
  ·
    refine ⟨206535071253572378284743035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137690047502381585523162023 206535071253572378284743035)
    ·
      refine ⟨309802606880358567427114553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206535071253572378284743035 309802606880358567427114553)
      ·
        refine ⟨232351955160268925570335915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309802606880358567427114553 232351955160268925570335915)
        ·
          refine ⟨348527932740403388355503873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232351955160268925570335915 348527932740403388355503873)
          ·
            refine ⟨261395949555302541266627905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348527932740403388355503873 261395949555302541266627905)
            ·
              refine ⟨196046962166476905949970929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261395949555302541266627905 196046962166476905949970929)
              ·
                refine ⟨147035221624857679462478197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196046962166476905949970929 147035221624857679462478197)
                ·
                  refine ⟨13784552027330407449607331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147035221624857679462478197 13784552027330407449607331)
                  ·
                    refine ⟨20676828040995611174410997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13784552027330407449607331 20676828040995611174410997)
                    ·
                      refine ⟨1938452628843338547601031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20676828040995611174410997 1938452628843338547601031)
                      ·
                        rfl

theorem cell23_3775123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 5].length) (baseStart_3775123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775123 prefixEnd_3775123 := by exact prefixLift 3775123
  have htrace : WordTrace (prefixWord ++ tailWord_3775123) baseStart_3775123 baseEnd_3775123 := by
    simpa [prefixWord, tailWord_3775123, baseEnd_3775123] using wordTrace_append hprefix tailTrace_3775123
  have hstable : (prefixWord ++ tailWord_3775123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775123).length < 2 ^ (prefixWord ++ tailWord_3775123).sum := by decide
  have hdescent : baseEnd_3775123 < baseStart_3775123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775124 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 4, 3, 2]
def baseStart_3775124 : Nat := 118140960795 + 3775124 * 2 ^ 59
def prefixEnd_3775124 : Nat := 4983230072969 + 3 ^ 40 * 3775124 * 2
def baseEnd_3775124 : Nat := 1938453142323993043688527

theorem tailTrace_3775124 : CollatzResearch.WordTrace tailWord_3775124 prefixEnd_3775124 1938453142323993043688527 := by
  unfold tailWord_3775124
  simp only [CollatzResearch.WordTrace]
  refine ⟨68845041987688981346974213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91793389316918641795965617 68845041987688981346974213)
  ·
    refine ⟨12908445372691684002557665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68845041987688981346974213 12908445372691684002557665)
    ·
      refine ⟨9681334029518763001918249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12908445372691684002557665 9681334029518763001918249)
      ·
        refine ⟨7261000522139072251438687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9681334029518763001918249 7261000522139072251438687)
        ·
          refine ⟨10891500783208608377158031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7261000522139072251438687 10891500783208608377158031)
          ·
            refine ⟨16337251174812912565737047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10891500783208608377158031 16337251174812912565737047)
            ·
              refine ⟨24505876762219368848605571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16337251174812912565737047 24505876762219368848605571)
              ·
                refine ⟨36758815143329053272908357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24505876762219368848605571 36758815143329053272908357)
                ·
                  refine ⟨6892277839374197488670317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36758815143329053272908357 6892277839374197488670317)
                  ·
                    refine ⟨2584604189765324058251369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6892277839374197488670317 2584604189765324058251369)
                    ·
                      refine ⟨1938453142323993043688527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2584604189765324058251369 1938453142323993043688527)
                      ·
                        rfl

theorem cell23_3775124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_3775124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775124 prefixEnd_3775124 := by exact prefixLift 3775124
  have htrace : WordTrace (prefixWord ++ tailWord_3775124) baseStart_3775124 baseEnd_3775124 := by
    simpa [prefixWord, tailWord_3775124, baseEnd_3775124] using wordTrace_append hprefix tailTrace_3775124
  have hstable : (prefixWord ++ tailWord_3775124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775124).length < 2 ^ (prefixWord ++ tailWord_3775124).sum := by decide
  have hdescent : baseEnd_3775124 < baseStart_3775124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775140 : List Nat := [2, 3, 1, 2, 2, 1, 1, 4, 1, 1, 5]
def baseStart_3775140 : Nat := 118140960795 + 3775140 * 2 ^ 59
def prefixEnd_3775140 : Nat := 4983230072969 + 3 ^ 40 * 3775140 * 2
def baseEnd_3775140 : Nat := 1938461358014464981088453

theorem tailTrace_3775140 : CollatzResearch.WordTrace tailWord_3775140 prefixEnd_3775140 1938461358014464981088453 := by
  unfold tailWord_3775140
  simp only [CollatzResearch.WordTrace]
  refine ⟨68845333771659998713265437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91793778362213331617687249 68845333771659998713265437)
  ·
    refine ⟨25817000164372499517474539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68845333771659998713265437 25817000164372499517474539)
    ·
      refine ⟨38725500246558749276211809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25817000164372499517474539 38725500246558749276211809)
      ·
        refine ⟨29044125184919061957158857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38725500246558749276211809 29044125184919061957158857)
        ·
          refine ⟨21783093888689296467869143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29044125184919061957158857 21783093888689296467869143)
          ·
            refine ⟨32674640833033944701803715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21783093888689296467869143 32674640833033944701803715)
            ·
              refine ⟨49011961249550917052705573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32674640833033944701803715 49011961249550917052705573)
              ·
                refine ⟨9189742734290796947382295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49011961249550917052705573 9189742734290796947382295)
                ·
                  refine ⟨13784614101436195421073443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9189742734290796947382295 13784614101436195421073443)
                  ·
                    refine ⟨20676921152154293131610165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13784614101436195421073443 20676921152154293131610165)
                    ·
                      refine ⟨1938461358014464981088453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20676921152154293131610165 1938461358014464981088453)
                      ·
                        rfl

theorem cell23_3775140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_3775140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775140 prefixEnd_3775140 := by exact prefixLift 3775140
  have htrace : WordTrace (prefixWord ++ tailWord_3775140) baseStart_3775140 baseEnd_3775140 := by
    simpa [prefixWord, tailWord_3775140, baseEnd_3775140] using wordTrace_append hprefix tailTrace_3775140
  have hstable : (prefixWord ++ tailWord_3775140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775140).length < 2 ^ (prefixWord ++ tailWord_3775140).sum := by decide
  have hdescent : baseEnd_3775140 < baseStart_3775140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775158 : List Nat := [5, 1, 3, 1, 2, 1, 2, 1, 2, 3, 2]
def baseStart_3775158 : Nat := 118140960795 + 3775158 * 2 ^ 59
def prefixEnd_3775158 : Nat := 4983230072969 + 3 ^ 40 * 3775158 * 2
def baseEnd_3775158 : Nat := 1938470600666245910663371

theorem tailTrace_3775158 : CollatzResearch.WordTrace tailWord_3775158 prefixEnd_3775158 1938470600666245910663371 := by
  unfold tailWord_3775158
  simp only [CollatzResearch.WordTrace]
  refine ⟨8605707753578424156292883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91794216038169857667124085 8605707753578424156292883)
  ·
    refine ⟨12908561630367636234439325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8605707753578424156292883 12908561630367636234439325)
    ·
      refine ⟨4840710611387863587914747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12908561630367636234439325 4840710611387863587914747)
      ·
        refine ⟨7261065917081795381872121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4840710611387863587914747 7261065917081795381872121)
        ·
          refine ⟨5445799437811346536404091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7261065917081795381872121 5445799437811346536404091)
          ·
            refine ⟨8168699156717019804606137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5445799437811346536404091 8168699156717019804606137)
            ·
              refine ⟨6126524367537764853454603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8168699156717019804606137 6126524367537764853454603)
              ·
                refine ⟨9189786551306647280181905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6126524367537764853454603 9189786551306647280181905)
                ·
                  refine ⟨6892339913479985460136429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9189786551306647280181905 6892339913479985460136429)
                  ·
                    refine ⟨2584627467554994547551161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6892339913479985460136429 2584627467554994547551161)
                    ·
                      refine ⟨1938470600666245910663371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2584627467554994547551161 1938470600666245910663371)
                      ·
                        rfl

theorem cell23_3775158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_3775158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775158 prefixEnd_3775158 := by exact prefixLift 3775158
  have htrace : WordTrace (prefixWord ++ tailWord_3775158) baseStart_3775158 baseEnd_3775158 := by
    simpa [prefixWord, tailWord_3775158, baseEnd_3775158] using wordTrace_append hprefix tailTrace_3775158
  have hstable : (prefixWord ++ tailWord_3775158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775158).length < 2 ^ (prefixWord ++ tailWord_3775158).sum := by decide
  have hdescent : baseEnd_3775158 < baseStart_3775158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775173 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 3, 9]
def baseStart_3775173 : Nat := 118140960795 + 3775173 * 2 ^ 59
def prefixEnd_3775173 : Nat := 4983230072969 + 3 ^ 40 * 3775173 * 2
def baseEnd_3775173 : Nat := 646159434292021117325267

theorem tailTrace_3775173 : CollatzResearch.WordTrace tailWord_3775173 prefixEnd_3775173 646159434292021117325267 := by
  unfold tailWord_3775173
  simp only [CollatzResearch.WordTrace]
  refine ⟨137691871152200444062482173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91794580768133629374988115 137691871152200444062482173)
  ·
    refine ⟨51634451682075166523430815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137691871152200444062482173 51634451682075166523430815)
    ·
      refine ⟨77451677523112749785146223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51634451682075166523430815 77451677523112749785146223)
      ·
        refine ⟨116177516284669124677719335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77451677523112749785146223 116177516284669124677719335)
        ·
          refine ⟨174266274427003687016579003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116177516284669124677719335 174266274427003687016579003)
          ·
            refine ⟨261399411640505530524868505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174266274427003687016579003 261399411640505530524868505)
            ·
              refine ⟨196049558730379147893651379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261399411640505530524868505 196049558730379147893651379)
              ·
                refine ⟨294074338095568721840477069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196049558730379147893651379 294074338095568721840477069)
                ·
                  refine ⟨110277876785838270690178901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 294074338095568721840477069 110277876785838270690178901)
                  ·
                    refine ⟨646159434292021117325267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 110277876785838270690178901 646159434292021117325267)
                    ·
                      rfl

theorem cell23_3775173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 9].length) (baseStart_3775173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775173 prefixEnd_3775173 := by exact prefixLift 3775173
  have htrace : WordTrace (prefixWord ++ tailWord_3775173) baseStart_3775173 baseEnd_3775173 := by
    simpa [prefixWord, tailWord_3775173, baseEnd_3775173] using wordTrace_append hprefix tailTrace_3775173
  have hstable : (prefixWord ++ tailWord_3775173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775173).length < 2 ^ (prefixWord ++ tailWord_3775173).sum := by decide
  have hdescent : baseEnd_3775173 < baseStart_3775173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775183 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 7]
def baseStart_3775183 : Nat := 118140960795 + 3775183 * 2 ^ 59
def prefixEnd_3775183 : Nat := 4983230072969 + 3 ^ 40 * 3775183 * 2
def baseEnd_3775183 : Nat := 1938483437682608312850755

theorem tailTrace_3775183 : CollatzResearch.WordTrace tailWord_3775183 prefixEnd_3775183 1938483437682608312850755 := by
  unfold tailWord_3775183
  simp only [CollatzResearch.WordTrace]
  refine ⟨137692235882164215770346203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91794823921442810513564135 137692235882164215770346203)
  ·
    refine ⟨206538353823246323655519305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137692235882164215770346203 206538353823246323655519305)
    ·
      refine ⟨154903765367434742741639479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206538353823246323655519305 154903765367434742741639479)
      ·
        refine ⟨232355648051152114112459219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154903765367434742741639479 232355648051152114112459219)
        ·
          refine ⟨348533472076728171168688829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232355648051152114112459219 348533472076728171168688829)
          ·
            refine ⟨130700052028773064188258311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 348533472076728171168688829 130700052028773064188258311)
            ·
              refine ⟨196050078043159596282387467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130700052028773064188258311 196050078043159596282387467)
              ·
                refine ⟨294075117064739394423581201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196050078043159596282387467 294075117064739394423581201)
                ·
                  refine ⟨220556337798554545817685901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 294075117064739394423581201 220556337798554545817685901)
                  ·
                    refine ⟨82708626674457954681632213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 220556337798554545817685901 82708626674457954681632213)
                    ·
                      refine ⟨1938483437682608312850755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 82708626674457954681632213 1938483437682608312850755)
                      ·
                        rfl

theorem cell23_3775183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 7].length) (baseStart_3775183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775183 prefixEnd_3775183 := by exact prefixLift 3775183
  have htrace : WordTrace (prefixWord ++ tailWord_3775183) baseStart_3775183 baseEnd_3775183 := by
    simpa [prefixWord, tailWord_3775183, baseEnd_3775183] using wordTrace_append hprefix tailTrace_3775183
  have hstable : (prefixWord ++ tailWord_3775183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775183).length < 2 ^ (prefixWord ++ tailWord_3775183).sum := by decide
  have hdescent : baseEnd_3775183 < baseStart_3775183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775204 : List Nat := [2, 3, 1, 1, 1, 4, 2, 3, 2, 1, 3]
def baseStart_3775204 : Nat := 118140960795 + 3775204 * 2 ^ 59
def prefixEnd_3775204 : Nat := 4983230072969 + 3 ^ 40 * 3775204 * 2
def baseEnd_3775204 : Nat := 1938494220776352730688159

theorem tailTrace_3775204 : CollatzResearch.WordTrace tailWord_3775204 prefixEnd_3775204 1938494220776352730688159 := by
  unfold tailWord_3775204
  simp only [CollatzResearch.WordTrace]
  refine ⟨68846500907544068178430333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91795334543392090904573777 68846500907544068178430333)
  ·
    refine ⟨25817437840329025566911375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68846500907544068178430333 25817437840329025566911375)
    ·
      refine ⟨38726156760493538350367063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25817437840329025566911375 38726156760493538350367063)
      ·
        refine ⟨58089235140740307525550595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38726156760493538350367063 58089235140740307525550595)
        ·
          refine ⟨87133852711110461288325893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58089235140740307525550595 87133852711110461288325893)
          ·
            refine ⟨16337597383333211491561105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87133852711110461288325893 16337597383333211491561105)
            ·
              refine ⟨12253198037499908618670829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16337597383333211491561105 12253198037499908618670829)
              ·
                refine ⟨4594949264062465732001561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12253198037499908618670829 4594949264062465732001561)
                ·
                  refine ⟨3446211948046849299001171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4594949264062465732001561 3446211948046849299001171)
                  ·
                    refine ⟨5169317922070273948501757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3446211948046849299001171 5169317922070273948501757)
                    ·
                      refine ⟨1938494220776352730688159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5169317922070273948501757 1938494220776352730688159)
                      ·
                        rfl

theorem cell23_3775204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 2, 1, 3].length) (baseStart_3775204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775204 prefixEnd_3775204 := by exact prefixLift 3775204
  have htrace : WordTrace (prefixWord ++ tailWord_3775204) baseStart_3775204 baseEnd_3775204 := by
    simpa [prefixWord, tailWord_3775204, baseEnd_3775204] using wordTrace_append hprefix tailTrace_3775204
  have hstable : (prefixWord ++ tailWord_3775204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775204).length < 2 ^ (prefixWord ++ tailWord_3775204).sum := by decide
  have hdescent : baseEnd_3775204 < baseStart_3775204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775210 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 4, 3, 4]
def baseStart_3775210 : Nat := 118140960795 + 3775210 * 2 ^ 59
def prefixEnd_3775210 : Nat := 4983230072969 + 3 ^ 40 * 3775210 * 2
def baseEnd_3775210 : Nat := 1938497301660279707213131

theorem tailTrace_3775210 : CollatzResearch.WordTrace tailWord_3775210 prefixEnd_3775210 1938497301660279707213131 := by
  unfold tailWord_3775210
  simp only [CollatzResearch.WordTrace]
  refine ⟨34423305163266599845394771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91795480435377599587719389 34423305163266599845394771)
  ·
    refine ⟨51634957744899899768092157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34423305163266599845394771 51634957744899899768092157)
    ·
      refine ⟨19363109154337462413034559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51634957744899899768092157 19363109154337462413034559)
      ·
        refine ⟨29044663731506193619551839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19363109154337462413034559 29044663731506193619551839)
        ·
          refine ⟨43566995597259290429327759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29044663731506193619551839 43566995597259290429327759)
          ·
            refine ⟨65350493395888935643991639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43566995597259290429327759 65350493395888935643991639)
            ·
              refine ⟨98025740093833403465987459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65350493395888935643991639 98025740093833403465987459)
              ·
                refine ⟨147038610140750105198981189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98025740093833403465987459 147038610140750105198981189)
                ·
                  refine ⟨27569739401390644724808973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147038610140750105198981189 27569739401390644724808973)
                  ·
                    refine ⟨10338652275521491771803365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27569739401390644724808973 10338652275521491771803365)
                    ·
                      refine ⟨1938497301660279707213131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10338652275521491771803365 1938497301660279707213131)
                      ·
                        rfl

theorem cell23_3775210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_3775210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775210 prefixEnd_3775210 := by exact prefixLift 3775210
  have htrace : WordTrace (prefixWord ++ tailWord_3775210) baseStart_3775210 baseEnd_3775210 := by
    simpa [prefixWord, tailWord_3775210, baseEnd_3775210] using wordTrace_append hprefix tailTrace_3775210
  have hstable : (prefixWord ++ tailWord_3775210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775210).length < 2 ^ (prefixWord ++ tailWord_3775210).sum := by decide
  have hdescent : baseEnd_3775210 < baseStart_3775210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775214 : List Nat := [4, 1, 2, 1, 1, 3, 2, 1, 3, 3, 2]
def baseStart_3775214 : Nat := 118140960795 + 3775214 * 2 ^ 59
def prefixEnd_3775214 : Nat := 4983230072969 + 3 ^ 40 * 3775214 * 2
def baseEnd_3775214 : Nat := 1938499355582897691563113

theorem tailTrace_3775214 : CollatzResearch.WordTrace tailWord_3775214 prefixEnd_3775214 1938499355582897691563113 := by
  unfold tailWord_3775214
  simp only [CollatzResearch.WordTrace]
  refine ⟨17211670818131488508090587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91795577696701272043149797 17211670818131488508090587)
  ·
    refine ⟨25817506227197232762135881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17211670818131488508090587 25817506227197232762135881)
    ·
      refine ⟨19363129670397924571601911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25817506227197232762135881 19363129670397924571601911)
      ·
        refine ⟨29044694505596886857402867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19363129670397924571601911 29044694505596886857402867)
        ·
          refine ⟨43567041758395330286104301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29044694505596886857402867 43567041758395330286104301)
          ·
            refine ⟨16337640659398248857289113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43567041758395330286104301 16337640659398248857289113)
            ·
              refine ⟨12253230494548686642966835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16337640659398248857289113 12253230494548686642966835)
              ·
                refine ⟨18379845741823029964450253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12253230494548686642966835 18379845741823029964450253)
                ·
                  refine ⟨6892442153183636236668845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18379845741823029964450253 6892442153183636236668845)
                  ·
                    refine ⟨2584665807443863588750817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6892442153183636236668845 2584665807443863588750817)
                    ·
                      refine ⟨1938499355582897691563113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2584665807443863588750817 1938499355582897691563113)
                      ·
                        rfl

theorem cell23_3775214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_3775214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775214 prefixEnd_3775214 := by exact prefixLift 3775214
  have htrace : WordTrace (prefixWord ++ tailWord_3775214) baseStart_3775214 baseEnd_3775214 := by
    simpa [prefixWord, tailWord_3775214, baseEnd_3775214] using wordTrace_append hprefix tailTrace_3775214
  have hstable : (prefixWord ++ tailWord_3775214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775214).length < 2 ^ (prefixWord ++ tailWord_3775214).sum := by decide
  have hdescent : baseEnd_3775214 < baseStart_3775214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775280 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 6, 5]
def baseStart_3775280 : Nat := 118140960795 + 3775280 * 2 ^ 59
def prefixEnd_3775280 : Nat := 4983230072969 + 3 ^ 40 * 3775280 * 2
def baseEnd_3775280 : Nat := 646177748435364811112603

theorem tailTrace_3775280 : CollatzResearch.WordTrace tailWord_3775280 prefixEnd_3775280 646177748435364811112603 := by
  unfold tailWord_3775280
  simp only [CollatzResearch.WordTrace]
  refine ⟨68847886881406400668313647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91797182508541867557751529 68847886881406400668313647)
  ·
    refine ⟨103271830322109601002470471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68847886881406400668313647 103271830322109601002470471)
    ·
      refine ⟨154907745483164401503705707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103271830322109601002470471 154907745483164401503705707)
      ·
        refine ⟨232361618224746602255558561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154907745483164401503705707 232361618224746602255558561)
        ·
          refine ⟨174271213668559951691668921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232361618224746602255558561 174271213668559951691668921)
          ·
            refine ⟨130703410251419963768751691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174271213668559951691668921 130703410251419963768751691)
            ·
              refine ⟨196055115377129945653127537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130703410251419963768751691 196055115377129945653127537)
              ·
                refine ⟨147041336532847459239845653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196055115377129945653127537 147041336532847459239845653)
                ·
                  refine ⟨6892562649977224651867765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 147041336532847459239845653 6892562649977224651867765)
                  ·
                    refine ⟨646177748435364811112603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6892562649977224651867765 646177748435364811112603)
                    ·
                      rfl

theorem cell23_3775280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 6, 5].length) (baseStart_3775280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775280 prefixEnd_3775280 := by exact prefixLift 3775280
  have htrace : WordTrace (prefixWord ++ tailWord_3775280) baseStart_3775280 baseEnd_3775280 := by
    simpa [prefixWord, tailWord_3775280, baseEnd_3775280] using wordTrace_append hprefix tailTrace_3775280
  have hstable : (prefixWord ++ tailWord_3775280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775280).length < 2 ^ (prefixWord ++ tailWord_3775280).sum := by decide
  have hdescent : baseEnd_3775280 < baseStart_3775280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775317 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 4, 1, 4]
def baseStart_3775317 : Nat := 118140960795 + 3775317 * 2 ^ 59
def prefixEnd_3775317 : Nat := 4983230072969 + 3 ^ 40 * 3775317 * 2
def baseEnd_3775317 : Nat := 1938552244090310788575139

theorem tailTrace_3775317 : CollatzResearch.WordTrace tailWord_3775317 prefixEnd_3775317 1938552244090310788575139 := by
  unfold tailWord_3775317
  simp only [CollatzResearch.WordTrace]
  refine ⟨137697123263678756655724205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91798082175785837770482803 137697123263678756655724205)
  ·
    refine ⟨51636421223879533745896577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137697123263678756655724205 51636421223879533745896577)
    ·
      refine ⟨38727315917909650309422433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51636421223879533745896577 38727315917909650309422433)
      ·
        refine ⟨29045486938432237732066825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38727315917909650309422433 29045486938432237732066825)
        ·
          refine ⟨21784115203824178299050119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29045486938432237732066825 21784115203824178299050119)
          ·
            refine ⟨32676172805736267448575179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21784115203824178299050119 32676172805736267448575179)
            ·
              refine ⟨49014259208604401172862769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32676172805736267448575179 49014259208604401172862769)
              ·
                refine ⟨36760694406453300879647077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49014259208604401172862769 36760694406453300879647077)
                ·
                  refine ⟨6892630201209993914933827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36760694406453300879647077 6892630201209993914933827)
                  ·
                    refine ⟨10338945301814990872400741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6892630201209993914933827 10338945301814990872400741)
                    ·
                      refine ⟨1938552244090310788575139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10338945301814990872400741 1938552244090310788575139)
                      ·
                        rfl

theorem cell23_3775317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_3775317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775317 prefixEnd_3775317 := by exact prefixLift 3775317
  have htrace : WordTrace (prefixWord ++ tailWord_3775317) baseStart_3775317 baseEnd_3775317 := by
    simpa [prefixWord, tailWord_3775317, baseEnd_3775317] using wordTrace_append hprefix tailTrace_3775317
  have hstable : (prefixWord ++ tailWord_3775317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775317).length < 2 ^ (prefixWord ++ tailWord_3775317).sum := by decide
  have hdescent : baseEnd_3775317 < baseStart_3775317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775320 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 1, 5, 5]
def baseStart_3775320 : Nat := 118140960795 + 3775320 * 2 ^ 59
def prefixEnd_3775320 : Nat := 4983230072969 + 3 ^ 40 * 3775320 * 2
def baseEnd_3775320 : Nat := 1938553784532274276837625

theorem tailTrace_3775320 : CollatzResearch.WordTrace tailWord_3775320 prefixEnd_3775320 1938553784532274276837625 := by
  unfold tailWord_3775320
  simp only [CollatzResearch.WordTrace]
  refine ⟨68848616341333944084041707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91798155121778592112055609 68848616341333944084041707)
  ·
    refine ⟨103272924512000916126062561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68848616341333944084041707 103272924512000916126062561)
    ·
      refine ⟨77454693384000687094546921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103272924512000916126062561 77454693384000687094546921)
      ·
        refine ⟨58091020038000515320910191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77454693384000687094546921 58091020038000515320910191)
        ·
          refine ⟨87136530057000772981365287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58091020038000515320910191 87136530057000772981365287)
          ·
            refine ⟨130704795085501159472047931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87136530057000772981365287 130704795085501159472047931)
            ·
              refine ⟨196057192628251739208071897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130704795085501159472047931 196057192628251739208071897)
              ·
                refine ⟨147042894471188804406053923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196057192628251739208071897 147042894471188804406053923)
                ·
                  refine ⟨220564341706783206609080885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147042894471188804406053923 220564341706783206609080885)
                  ·
                    refine ⟨20677907035010925619601333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 220564341706783206609080885 20677907035010925619601333)
                    ·
                      refine ⟨1938553784532274276837625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20677907035010925619601333 1938553784532274276837625)
                      ·
                        rfl

theorem cell23_3775320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_3775320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775320 prefixEnd_3775320 := by exact prefixLift 3775320
  have htrace : WordTrace (prefixWord ++ tailWord_3775320) baseStart_3775320 baseEnd_3775320 := by
    simpa [prefixWord, tailWord_3775320, baseEnd_3775320] using wordTrace_append hprefix tailTrace_3775320
  have hstable : (prefixWord ++ tailWord_3775320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775320).length < 2 ^ (prefixWord ++ tailWord_3775320).sum := by decide
  have hdescent : baseEnd_3775320 < baseStart_3775320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775327 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 5, 4]
def baseStart_3775327 : Nat := 118140960795 + 3775327 * 2 ^ 59
def prefixEnd_3775327 : Nat := 4983230072969 + 3 ^ 40 * 3775327 * 2
def baseEnd_3775327 : Nat := 646185792965618583150031

theorem tailTrace_3775327 : CollatzResearch.WordTrace tailWord_3775327 prefixEnd_3775327 646185792965618583150031 := by
  unfold tailWord_3775327
  simp only [CollatzResearch.WordTrace]
  refine ⟨137697487993642528363588235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91798325329095018909058823 137697487993642528363588235)
  ·
    refine ⟨206546231990463792545382353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137697487993642528363588235 206546231990463792545382353)
    ·
      refine ⟨154909673992847844409036765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206546231990463792545382353 154909673992847844409036765)
      ·
        refine ⟨58091127747317941653388787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154909673992847844409036765 58091127747317941653388787)
        ·
          refine ⟨87136691620976912480083181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58091127747317941653388787 87136691620976912480083181)
          ·
            refine ⟨32676259357866342180031193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87136691620976912480083181 32676259357866342180031193)
            ·
              refine ⟨24507194518399756635023395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32676259357866342180031193 24507194518399756635023395)
              ·
                refine ⟨36760791777599634952535093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24507194518399756635023395 36760791777599634952535093)
                ·
                  refine ⟨3446324229149965776800165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36760791777599634952535093 3446324229149965776800165)
                  ·
                    refine ⟨646185792965618583150031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3446324229149965776800165 646185792965618583150031)
                    ·
                      rfl

theorem cell23_3775327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 5, 4].length) (baseStart_3775327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775327 prefixEnd_3775327 := by exact prefixLift 3775327
  have htrace : WordTrace (prefixWord ++ tailWord_3775327) baseStart_3775327 baseEnd_3775327 := by
    simpa [prefixWord, tailWord_3775327, baseEnd_3775327] using wordTrace_append hprefix tailTrace_3775327
  have hstable : (prefixWord ++ tailWord_3775327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775327).length < 2 ^ (prefixWord ++ tailWord_3775327).sum := by decide
  have hdescent : baseEnd_3775327 < baseStart_3775327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775357 : List Nat := [1, 4, 1, 1, 2, 1, 3, 4, 6]
def baseStart_3775357 : Nat := 118140960795 + 3775357 * 2 ^ 59
def prefixEnd_3775357 : Nat := 4983230072969 + 3 ^ 40 * 3775357 * 2
def baseEnd_3775357 : Nat := 215396975924054514674995

theorem tailTrace_3775357 : CollatzResearch.WordTrace tailWord_3775357 prefixEnd_3775357 215396975924054514674995 := by
  unfold tailWord_3775357
  simp only [CollatzResearch.WordTrace]
  refine ⟨137698582183533843487180325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91799054789022562324786883 137698582183533843487180325)
  ·
    refine ⟨25818484159412595653846311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137698582183533843487180325 25818484159412595653846311)
    ·
      refine ⟨38727726239118893480769467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25818484159412595653846311 38727726239118893480769467)
      ·
        refine ⟨58091589358678340221154201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38727726239118893480769467 58091589358678340221154201)
        ·
          refine ⟨43568692019008755165865651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58091589358678340221154201 43568692019008755165865651)
          ·
            refine ⟨65353038028513132748798477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43568692019008755165865651 65353038028513132748798477)
            ·
              refine ⟨24507389260692424780799429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65353038028513132748798477 24507389260692424780799429)
              ·
                refine ⟨4595135486379829646399893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24507389260692424780799429 4595135486379829646399893)
                ·
                  refine ⟨215396975924054514674995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4595135486379829646399893 215396975924054514674995)
                  ·
                    rfl

theorem cell23_3775357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 6].length) (baseStart_3775357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775357 prefixEnd_3775357 := by exact prefixLift 3775357
  have htrace : WordTrace (prefixWord ++ tailWord_3775357) baseStart_3775357 baseEnd_3775357 := by
    simpa [prefixWord, tailWord_3775357, baseEnd_3775357] using wordTrace_append hprefix tailTrace_3775357
  have hstable : (prefixWord ++ tailWord_3775357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775357).length < 2 ^ (prefixWord ++ tailWord_3775357).sum := by decide
  have hdescent : baseEnd_3775357 < baseStart_3775357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775388 : List Nat := [2, 2, 3, 3, 2, 2, 1, 1, 2, 2, 3]
def baseStart_3775388 : Nat := 118140960795 + 3775388 * 2 ^ 59
def prefixEnd_3775388 : Nat := 4983230072969 + 3 ^ 40 * 3775388 * 2
def baseEnd_3775388 : Nat := 1938588701216780010787313

theorem tailTrace_3775388 : CollatzResearch.WordTrace tailWord_3775388 prefixEnd_3775388 1938588701216780010787313 := by
  unfold tailWord_3775388
  simp only [CollatzResearch.WordTrace]
  refine ⟨68849856423210767890779409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91799808564281023854372545 68849856423210767890779409)
  ·
    refine ⟨51637392317408075918084557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68849856423210767890779409 51637392317408075918084557)
    ·
      refine ⟨19364022119028028469281709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51637392317408075918084557 19364022119028028469281709)
      ·
        refine ⟨7261508294635510675980641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19364022119028028469281709 7261508294635510675980641)
        ·
          refine ⟨5446131220976633006985481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7261508294635510675980641 5446131220976633006985481)
          ·
            refine ⟨4084598415732474755239111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5446131220976633006985481 4084598415732474755239111)
            ·
              refine ⟨6126897623598712132858667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4084598415732474755239111 6126897623598712132858667)
              ·
                refine ⟨9190346435398068199288001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6126897623598712132858667 9190346435398068199288001)
                ·
                  refine ⟨6892759826548551149466001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9190346435398068199288001 6892759826548551149466001)
                  ·
                    refine ⟨5169569869911413362099501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6892759826548551149466001 5169569869911413362099501)
                    ·
                      refine ⟨1938588701216780010787313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5169569869911413362099501 1938588701216780010787313)
                      ·
                        rfl

theorem cell23_3775388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_3775388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775388 prefixEnd_3775388 := by exact prefixLift 3775388
  have htrace : WordTrace (prefixWord ++ tailWord_3775388) baseStart_3775388 baseEnd_3775388 := by
    simpa [prefixWord, tailWord_3775388, baseEnd_3775388] using wordTrace_append hprefix tailTrace_3775388
  have hstable : (prefixWord ++ tailWord_3775388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775388).length < 2 ^ (prefixWord ++ tailWord_3775388).sum := by decide
  have hdescent : baseEnd_3775388 < baseStart_3775388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775407 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 4]
def baseStart_3775407 : Nat := 118140960795 + 3775407 * 2 ^ 59
def prefixEnd_3775407 : Nat := 4983230072969 + 3 ^ 40 * 3775407 * 2
def baseEnd_3775407 : Nat := 1938598457349215436449725

theorem tailTrace_3775407 : CollatzResearch.WordTrace tailWord_3775407 prefixEnd_3775407 1938598457349215436449725 := by
  unfold tailWord_3775407
  simp only [CollatzResearch.WordTrace]
  refine ⟨137700405833352702026500475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91800270555568468017666983 137700405833352702026500475)
  ·
    refine ⟨206550608750029053039750713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137700405833352702026500475 206550608750029053039750713)
    ·
      refine ⟨154912956562521789779813035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206550608750029053039750713 154912956562521789779813035)
      ·
        refine ⟨232369434843782684669719553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154912956562521789779813035 232369434843782684669719553)
        ·
          refine ⟨174277076132837013502289665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232369434843782684669719553 174277076132837013502289665)
          ·
            refine ⟨130707807099627760126717249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174277076132837013502289665 130707807099627760126717249)
            ·
              refine ⟨98030855324720820095037937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130707807099627760126717249 98030855324720820095037937)
              ·
                refine ⟨73523141493540615071278453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98030855324720820095037937 73523141493540615071278453)
                ·
                  refine ⟨6892794515019432662932355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73523141493540615071278453 6892794515019432662932355)
                  ·
                    refine ⟨10339191772529148994398533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6892794515019432662932355 10339191772529148994398533)
                    ·
                      refine ⟨1938598457349215436449725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10339191772529148994398533 1938598457349215436449725)
                      ·
                        rfl

theorem cell23_3775407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 4].length) (baseStart_3775407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775407 prefixEnd_3775407 := by exact prefixLift 3775407
  have htrace : WordTrace (prefixWord ++ tailWord_3775407) baseStart_3775407 baseEnd_3775407 := by
    simpa [prefixWord, tailWord_3775407, baseEnd_3775407] using wordTrace_append hprefix tailTrace_3775407
  have hstable : (prefixWord ++ tailWord_3775407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775407).length < 2 ^ (prefixWord ++ tailWord_3775407).sum := by decide
  have hdescent : baseEnd_3775407 < baseStart_3775407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775427 : List Nat := [1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 5]
def baseStart_3775427 : Nat := 118140960795 + 3775427 * 2 ^ 59
def prefixEnd_3775427 : Nat := 4983230072969 + 3 ^ 40 * 3775427 * 2
def baseEnd_3775427 : Nat := 1938608726962305358199633

theorem tailTrace_3775427 : CollatzResearch.WordTrace tailWord_3775427 prefixEnd_3775427 1938608726962305358199633 := by
  unfold tailWord_3775427
  simp only [CollatzResearch.WordTrace]
  refine ⟨137701135293280245442228535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91800756862186830294819023 137701135293280245442228535)
  ·
    refine ⟨206551702939920368163342803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137701135293280245442228535 206551702939920368163342803)
    ·
      refine ⟨309827554409880552245014205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206551702939920368163342803 309827554409880552245014205)
      ·
        refine ⟨116185332903705207091880327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309827554409880552245014205 116185332903705207091880327)
        ·
          refine ⟨174277999355557810637820491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116185332903705207091880327 174277999355557810637820491)
          ·
            refine ⟨261416999033336715956730737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174277999355557810637820491 261416999033336715956730737)
            ·
              refine ⟨196062749275002536967548053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261416999033336715956730737 196062749275002536967548053)
              ·
                refine ⟨9190441372265743920353815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 196062749275002536967548053 9190441372265743920353815)
                ·
                  refine ⟨13785662058398615880530723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9190441372265743920353815 13785662058398615880530723)
                  ·
                    refine ⟨20678493087597923820796085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13785662058398615880530723 20678493087597923820796085)
                    ·
                      refine ⟨1938608726962305358199633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20678493087597923820796085 1938608726962305358199633)
                      ·
                        rfl

theorem cell23_3775427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 5].length) (baseStart_3775427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775427 prefixEnd_3775427 := by exact prefixLift 3775427
  have htrace : WordTrace (prefixWord ++ tailWord_3775427) baseStart_3775427 baseEnd_3775427 := by
    simpa [prefixWord, tailWord_3775427, baseEnd_3775427] using wordTrace_append hprefix tailTrace_3775427
  have hstable : (prefixWord ++ tailWord_3775427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775427).length < 2 ^ (prefixWord ++ tailWord_3775427).sum := by decide
  have hdescent : baseEnd_3775427 < baseStart_3775427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775441 : List Nat := [1, 2, 2, 1, 2, 1, 3, 4, 3, 2, 2]
def baseStart_3775441 : Nat := 118140960795 + 3775441 * 2 ^ 59
def prefixEnd_3775441 : Nat := 4983230072969 + 3 ^ 40 * 3775441 * 2
def baseEnd_3775441 : Nat := 1938615915691468303424569

theorem tailTrace_3775441 : CollatzResearch.WordTrace tailWord_3775441 prefixEnd_3775441 1938615915691468303424569 := by
  unfold tailWord_3775441
  simp only [CollatzResearch.WordTrace]
  refine ⟨137701645915229525833238177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91801097276819683888825451 137701645915229525833238177)
  ·
    refine ⟨103276234436422144374928633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137701645915229525833238177 103276234436422144374928633)
    ·
      refine ⟨77457175827316608281196475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103276234436422144374928633 77457175827316608281196475)
      ·
        refine ⟨116185763740974912421794713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77457175827316608281196475 116185763740974912421794713)
        ·
          refine ⟨87139322805731184316346035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116185763740974912421794713 87139322805731184316346035)
          ·
            refine ⟨130708984208596776474519053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87139322805731184316346035 130708984208596776474519053)
            ·
              refine ⟨49015869078223791177944645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130708984208596776474519053 49015869078223791177944645)
              ·
                refine ⟨9190475452166960845864621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49015869078223791177944645 9190475452166960845864621)
                ·
                  refine ⟨3446428294562610317199233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9190475452166960845864621 3446428294562610317199233)
                  ·
                    refine ⟨2584821220921957737899425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3446428294562610317199233 2584821220921957737899425)
                    ·
                      refine ⟨1938615915691468303424569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2584821220921957737899425 1938615915691468303424569)
                      ·
                        rfl

theorem cell23_3775441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 3, 2, 2].length) (baseStart_3775441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775441 prefixEnd_3775441 := by exact prefixLift 3775441
  have htrace : WordTrace (prefixWord ++ tailWord_3775441) baseStart_3775441 baseEnd_3775441 := by
    simpa [prefixWord, tailWord_3775441, baseEnd_3775441] using wordTrace_append hprefix tailTrace_3775441
  have hstable : (prefixWord ++ tailWord_3775441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775441).length < 2 ^ (prefixWord ++ tailWord_3775441).sum := by decide
  have hdescent : baseEnd_3775441 < baseStart_3775441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775458 : List Nat := [3, 3, 3, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_3775458 : Nat := 118140960795 + 3775458 * 2 ^ 59
def prefixEnd_3775458 : Nat := 4983230072969 + 3 ^ 40 * 3775458 * 2
def baseEnd_3775458 : Nat := 1938624644862594736911991

theorem tailTrace_3775458 : CollatzResearch.WordTrace tailWord_3775458 prefixEnd_3775458 1938624644862594736911991 := by
  unfold tailWord_3775458
  simp only [CollatzResearch.WordTrace]
  refine ⟨34425566489041984434151757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91801510637445291824404685 34425566489041984434151757)
  ·
    refine ⟨12909587433390744162806909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34425566489041984434151757 12909587433390744162806909)
    ·
      refine ⟨4841095287521529061052591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12909587433390744162806909 4841095287521529061052591)
      ·
        refine ⟨7261642931282293591578887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4841095287521529061052591 7261642931282293591578887)
        ·
          refine ⟨10892464396923440387368331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7261642931282293591578887 10892464396923440387368331)
          ·
            refine ⟨16338696595385160581052497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10892464396923440387368331 16338696595385160581052497)
            ·
              refine ⟨12254022446538870435789373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16338696595385160581052497 12254022446538870435789373)
              ·
                refine ⟨4595258417452076413421015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12254022446538870435789373 4595258417452076413421015)
                ·
                  refine ⟨6892887626178114620131523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4595258417452076413421015 6892887626178114620131523)
                  ·
                    refine ⟨10339331439267171930197285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6892887626178114620131523 10339331439267171930197285)
                    ·
                      refine ⟨1938624644862594736911991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10339331439267171930197285 1938624644862594736911991)
                      ·
                        rfl

theorem cell23_3775458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_3775458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775458 prefixEnd_3775458 := by exact prefixLift 3775458
  have htrace : WordTrace (prefixWord ++ tailWord_3775458) baseStart_3775458 baseEnd_3775458 := by
    simpa [prefixWord, tailWord_3775458, baseEnd_3775458] using wordTrace_append hprefix tailTrace_3775458
  have hstable : (prefixWord ++ tailWord_3775458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775458).length < 2 ^ (prefixWord ++ tailWord_3775458).sum := by decide
  have hdescent : baseEnd_3775458 < baseStart_3775458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775507 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 4, 6]
def baseStart_3775507 : Nat := 118140960795 + 3775507 * 2 ^ 59
def prefixEnd_3775507 : Nat := 4983230072969 + 3 ^ 40 * 3775507 * 2
def baseEnd_3775507 : Nat := 646216601804888348399755

theorem tailTrace_3775507 : CollatzResearch.WordTrace tailWord_3775507 prefixEnd_3775507 646216601804888348399755 := by
  unfold tailWord_3775507
  simp only [CollatzResearch.WordTrace]
  refine ⟨137704053132990419105140775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91802702088660279403427183 137704053132990419105140775)
  ·
    refine ⟨206556079699485628657711163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137704053132990419105140775 206556079699485628657711163)
    ·
      refine ⟨309834119549228442986566745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206556079699485628657711163 309834119549228442986566745)
      ·
        refine ⟨232375589661921332239925059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309834119549228442986566745 232375589661921332239925059)
        ·
          refine ⟨348563384492881998359887589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232375589661921332239925059 348563384492881998359887589)
          ·
            refine ⟨65355634592415374692478923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 348563384492881998359887589 65355634592415374692478923)
            ·
              refine ⟨98033451888623062038718385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65355634592415374692478923 98033451888623062038718385)
              ·
                refine ⟨73525088916467296529038789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98033451888623062038718385 73525088916467296529038789)
                ·
                  refine ⟨13785954171837618099194773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73525088916467296529038789 13785954171837618099194773)
                  ·
                    refine ⟨646216601804888348399755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13785954171837618099194773 646216601804888348399755)
                    ·
                      rfl

theorem cell23_3775507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 6].length) (baseStart_3775507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775507 prefixEnd_3775507 := by exact prefixLift 3775507
  have htrace : WordTrace (prefixWord ++ tailWord_3775507) baseStart_3775507 baseEnd_3775507 := by
    simpa [prefixWord, tailWord_3775507, baseEnd_3775507] using wordTrace_append hprefix tailTrace_3775507
  have hstable : (prefixWord ++ tailWord_3775507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775507).length < 2 ^ (prefixWord ++ tailWord_3775507).sum := by decide
  have hdescent : baseEnd_3775507 < baseStart_3775507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775544 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 1, 4, 4]
def baseStart_3775544 : Nat := 118140960795 + 3775544 * 2 ^ 59
def prefixEnd_3775544 : Nat := 4983230072969 + 3 ^ 40 * 3775544 * 2
def baseEnd_3775544 : Nat := 1938668804198881400436595

theorem tailTrace_3775544 : CollatzResearch.WordTrace tailWord_3775544 prefixEnd_3775544 1938668804198881400436595 := by
  unfold tailWord_3775544
  simp only [CollatzResearch.WordTrace]
  refine ⟨68852701316928187212118843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91803601755904249616158457 68852701316928187212118843)
  ·
    refine ⟨103279051975392280818178265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68852701316928187212118843 103279051975392280818178265)
    ·
      refine ⟨77459288981544210613633699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103279051975392280818178265 77459288981544210613633699)
      ·
        refine ⟨116188933472316315920450549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77459288981544210613633699 116188933472316315920450549)
        ·
          refine ⟨10892712513029654617542239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116188933472316315920450549 10892712513029654617542239)
          ·
            refine ⟨16339068769544481926313359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10892712513029654617542239 16339068769544481926313359)
            ·
              refine ⟨24508603154316722889470039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16339068769544481926313359 24508603154316722889470039)
              ·
                refine ⟨36762904731475084334205059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24508603154316722889470039 36762904731475084334205059)
                ·
                  refine ⟨55144357097212626501307589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36762904731475084334205059 55144357097212626501307589)
                  ·
                    refine ⟨10339566955727367468995173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55144357097212626501307589 10339566955727367468995173)
                    ·
                      refine ⟨1938668804198881400436595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10339566955727367468995173 1938668804198881400436595)
                      ·
                        rfl

theorem cell23_3775544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_3775544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775544 prefixEnd_3775544 := by exact prefixLift 3775544
  have htrace : WordTrace (prefixWord ++ tailWord_3775544) baseStart_3775544 baseEnd_3775544 := by
    simpa [prefixWord, tailWord_3775544, baseEnd_3775544] using wordTrace_append hprefix tailTrace_3775544
  have hstable : (prefixWord ++ tailWord_3775544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775544).length < 2 ^ (prefixWord ++ tailWord_3775544).sum := by decide
  have hdescent : baseEnd_3775544 < baseStart_3775544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775548 : List Nat := [2, 2, 2, 2, 2, 3, 2, 1, 1, 4, 2]
def baseStart_3775548 : Nat := 118140960795 + 3775548 * 2 ^ 59
def prefixEnd_3775548 : Nat := 4983230072969 + 3 ^ 40 * 3775548 * 2
def baseEnd_3775548 : Nat := 1938670858121499384786577

theorem tailTrace_3775548 : CollatzResearch.WordTrace tailWord_3775548 prefixEnd_3775548 1938670858121499384786577 := by
  unfold tailWord_3775548
  simp only [CollatzResearch.WordTrace]
  refine ⟨68852774262920941553691649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91803699017227922071588865 68852774262920941553691649)
  ·
    refine ⟨51639580697190706165268737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68852774262920941553691649 51639580697190706165268737)
    ·
      refine ⟨38729685522893029623951553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51639580697190706165268737 38729685522893029623951553)
      ·
        refine ⟨29047264142169772217963665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38729685522893029623951553 29047264142169772217963665)
        ·
          refine ⟨21785448106627329163472749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29047264142169772217963665 21785448106627329163472749)
          ·
            refine ⟨8169543039985248436302281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21785448106627329163472749 8169543039985248436302281)
            ·
              refine ⟨6127157279988936327226711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8169543039985248436302281 6127157279988936327226711)
              ·
                refine ⟨9190735919983404490840067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6127157279988936327226711 9190735919983404490840067)
                ·
                  refine ⟨13786103879975106736260101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9190735919983404490840067 13786103879975106736260101)
                  ·
                    refine ⟨2584894477495332513048769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13786103879975106736260101 2584894477495332513048769)
                    ·
                      refine ⟨1938670858121499384786577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2584894477495332513048769 1938670858121499384786577)
                      ·
                        rfl

theorem cell23_3775548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_3775548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775548 prefixEnd_3775548 := by exact prefixLift 3775548
  have htrace : WordTrace (prefixWord ++ tailWord_3775548) baseStart_3775548 baseEnd_3775548 := by
    simpa [prefixWord, tailWord_3775548, baseEnd_3775548] using wordTrace_append hprefix tailTrace_3775548
  have hstable : (prefixWord ++ tailWord_3775548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775548).length < 2 ^ (prefixWord ++ tailWord_3775548).sum := by decide
  have hdescent : baseEnd_3775548 < baseStart_3775548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775564 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 3, 5, 3]
def baseStart_3775564 : Nat := 118140960795 + 3775564 * 2 ^ 59
def prefixEnd_3775564 : Nat := 4983230072969 + 3 ^ 40 * 3775564 * 2
def baseEnd_3775564 : Nat := 1938679073811971322186503

theorem tailTrace_3775564 : CollatzResearch.WordTrace tailWord_3775564 prefixEnd_3775564 1938679073811971322186503 := by
  unfold tailWord_3775564
  simp only [CollatzResearch.WordTrace]
  refine ⟨68853066046891958919982873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91804088062522611893310497 68853066046891958919982873)
  ·
    refine ⟨51639799535168969189987155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68853066046891958919982873 51639799535168969189987155)
    ·
      refine ⟨77459699302753453784980733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51639799535168969189987155 77459699302753453784980733)
      ·
        refine ⟨29047387238532545169367775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77459699302753453784980733 29047387238532545169367775)
        ·
          refine ⟨43571080857798817754051663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29047387238532545169367775 43571080857798817754051663)
          ·
            refine ⟨65356621286698226631077495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43571080857798817754051663 65356621286698226631077495)
            ·
              refine ⟨98034931930047339946616243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65356621286698226631077495 98034931930047339946616243)
              ·
                refine ⟨147052397895071009919924365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98034931930047339946616243 147052397895071009919924365)
                ·
                  refine ⟨55144649210651628719971637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 147052397895071009919924365 55144649210651628719971637)
                  ·
                    refine ⟨5169810863498590192497341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55144649210651628719971637 5169810863498590192497341)
                    ·
                      refine ⟨1938679073811971322186503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5169810863498590192497341 1938679073811971322186503)
                      ·
                        rfl

theorem cell23_3775564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_3775564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775564 prefixEnd_3775564 := by exact prefixLift 3775564
  have htrace : WordTrace (prefixWord ++ tailWord_3775564) baseStart_3775564 baseEnd_3775564 := by
    simpa [prefixWord, tailWord_3775564, baseEnd_3775564] using wordTrace_append hprefix tailTrace_3775564
  have hstable : (prefixWord ++ tailWord_3775564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775564).length < 2 ^ (prefixWord ++ tailWord_3775564).sum := by decide
  have hdescent : baseEnd_3775564 < baseStart_3775564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775584 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 4, 5]
def baseStart_3775584 : Nat := 118140960795 + 3775584 * 2 ^ 59
def prefixEnd_3775584 : Nat := 4983230072969 + 3 ^ 40 * 3775584 * 2
def baseEnd_3775584 : Nat := 646229781141687081312137

theorem tailTrace_3775584 : CollatzResearch.WordTrace tailWord_3775584 prefixEnd_3775584 646229781141687081312137 := by
  unfold tailWord_3775584
  simp only [CollatzResearch.WordTrace]
  refine ⟨68853430776855730627846903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91804574369140974170462537 68853430776855730627846903)
  ·
    refine ⟨103280146165283595941770355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68853430776855730627846903 103280146165283595941770355)
    ·
      refine ⟨154920219247925393912655533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103280146165283595941770355 154920219247925393912655533)
      ·
        refine ⟨58095082217972022717245825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154920219247925393912655533 58095082217972022717245825)
        ·
          refine ⟨43571311663479017037934369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58095082217972022717245825 43571311663479017037934369)
          ·
            refine ⟨32678483747609262778450777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43571311663479017037934369 32678483747609262778450777)
            ·
              refine ⟨24508862810706947083838083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32678483747609262778450777 24508862810706947083838083)
              ·
                refine ⟨36763294216060420625757125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24508862810706947083838083 36763294216060420625757125)
                ·
                  refine ⟨6893117665511328867329461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36763294216060420625757125 6893117665511328867329461)
                  ·
                    refine ⟨646229781141687081312137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6893117665511328867329461 646229781141687081312137)
                    ·
                      rfl

theorem cell23_3775584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 4, 5].length) (baseStart_3775584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775584 prefixEnd_3775584 := by exact prefixLift 3775584
  have htrace : WordTrace (prefixWord ++ tailWord_3775584) baseStart_3775584 baseEnd_3775584 := by
    simpa [prefixWord, tailWord_3775584, baseEnd_3775584] using wordTrace_append hprefix tailTrace_3775584
  have hstable : (prefixWord ++ tailWord_3775584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775584).length < 2 ^ (prefixWord ++ tailWord_3775584).sum := by decide
  have hdescent : baseEnd_3775584 < baseStart_3775584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775711 : List Nat := [1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 4]
def baseStart_3775711 : Nat := 118140960795 + 3775711 * 2 ^ 59
def prefixEnd_3775711 : Nat := 4983230072969 + 3 ^ 40 * 3775711 * 2
def baseEnd_3775711 : Nat := 1938754555468182247048327

theorem tailTrace_3775711 : CollatzResearch.WordTrace tailWord_3775711 prefixEnd_3775711 1938754555468182247048327 := by
  unfold tailWord_3775711
  simp only [CollatzResearch.WordTrace]
  refine ⟨137711493624251361945566987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91807662416167574630377991 137711493624251361945566987)
  ·
    refine ⟨206567240436377042918350481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137711493624251361945566987 206567240436377042918350481)
    ·
      refine ⟨154925430327282782188762861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206567240436377042918350481 154925430327282782188762861)
      ·
        refine ⟨58097036372731043320786073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154925430327282782188762861 58097036372731043320786073)
        ·
          refine ⟨43572777279548282490589555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58097036372731043320786073 43572777279548282490589555)
          ·
            refine ⟨65359165919322423735884333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43572777279548282490589555 65359165919322423735884333)
            ·
              refine ⟨24509687219745908900956625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65359165919322423735884333 24509687219745908900956625)
              ·
                refine ⟨18382265414809431675717469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24509687219745908900956625 18382265414809431675717469)
                ·
                  refine ⟨6893349530553536878394051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18382265414809431675717469 6893349530553536878394051)
                  ·
                    refine ⟨10340024295830305317591077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6893349530553536878394051 10340024295830305317591077)
                    ·
                      refine ⟨1938754555468182247048327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10340024295830305317591077 1938754555468182247048327)
                      ·
                        rfl

theorem cell23_3775711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_3775711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775711 prefixEnd_3775711 := by exact prefixLift 3775711
  have htrace : WordTrace (prefixWord ++ tailWord_3775711) baseStart_3775711 baseEnd_3775711 := by
    simpa [prefixWord, tailWord_3775711, baseEnd_3775711] using wordTrace_append hprefix tailTrace_3775711
  have hstable : (prefixWord ++ tailWord_3775711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775711).length < 2 ^ (prefixWord ++ tailWord_3775711).sum := by decide
  have hdescent : baseEnd_3775711 < baseStart_3775711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775742 : List Nat := [4, 2, 2, 1, 1, 4, 2, 1, 1, 5]
def baseStart_3775742 : Nat := 118140960795 + 3775742 * 2 ^ 59
def prefixEnd_3775742 : Nat := 4983230072969 + 3 ^ 40 * 3775742 * 2
def baseEnd_3775742 : Nat := 646256824456157208586895

theorem tailTrace_3775742 : CollatzResearch.WordTrace tailWord_3775742 prefixEnd_3775742 646256824456157208586895 := by
  unfold tailWord_3775742
  simp only [CollatzResearch.WordTrace]
  refine ⟨17214078035892381779993185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91808416191426036159963653 17214078035892381779993185)
  ·
    refine ⟨12910558526919286334994889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17214078035892381779993185 12910558526919286334994889)
    ·
      refine ⟨9682918895189464751246167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12910558526919286334994889 9682918895189464751246167)
      ·
        refine ⟨14524378342784197126869251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9682918895189464751246167 14524378342784197126869251)
        ·
          refine ⟨21786567514176295690303877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14524378342784197126869251 21786567514176295690303877)
          ·
            refine ⟨4084981408908055441931977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21786567514176295690303877 4084981408908055441931977)
            ·
              refine ⟨3063736056681041581448983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4084981408908055441931977 3063736056681041581448983)
              ·
                refine ⟨4595604085021562372173475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3063736056681041581448983 4595604085021562372173475)
                ·
                  refine ⟨6893406127532343558260213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4595604085021562372173475 6893406127532343558260213)
                  ·
                    refine ⟨646256824456157208586895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6893406127532343558260213 646256824456157208586895)
                    ·
                      rfl

theorem cell23_3775742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_3775742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775742 prefixEnd_3775742 := by exact prefixLift 3775742
  have htrace : WordTrace (prefixWord ++ tailWord_3775742) baseStart_3775742 baseEnd_3775742 := by
    simpa [prefixWord, tailWord_3775742, baseEnd_3775742] using wordTrace_append hprefix tailTrace_3775742
  have hstable : (prefixWord ++ tailWord_3775742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775742).length < 2 ^ (prefixWord ++ tailWord_3775742).sum := by decide
  have hdescent : baseEnd_3775742 < baseStart_3775742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775745 : List Nat := [1, 2, 4, 1, 1, 3, 4, 1, 1, 1, 4]
def baseStart_3775745 : Nat := 118140960795 + 3775745 * 2 ^ 59
def prefixEnd_3775745 : Nat := 4983230072969 + 3 ^ 40 * 3775745 * 2
def baseEnd_3775745 : Nat := 1938772013810435114023171

theorem tailTrace_3775745 : CollatzResearch.WordTrace tailWord_3775745 prefixEnd_3775745 1938772013810435114023171 := by
  unfold tailWord_3775745
  simp only [CollatzResearch.WordTrace]
  refine ⟨137712733706128185752304689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91808489137418790501536459 137712733706128185752304689)
  ·
    refine ⟨103284550279596139314228517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137712733706128185752304689 103284550279596139314228517)
    ·
      refine ⟨19365853177424276121417847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103284550279596139314228517 19365853177424276121417847)
      ·
        refine ⟨29048779766136414182126771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19365853177424276121417847 29048779766136414182126771)
        ·
          refine ⟨43573169649204621273190157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29048779766136414182126771 43573169649204621273190157)
          ·
            refine ⟨16339938618451732977446309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43573169649204621273190157 16339938618451732977446309)
            ·
              refine ⟨3063738490959699933271183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16339938618451732977446309 3063738490959699933271183)
              ·
                refine ⟨4595607736439549899906775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3063738490959699933271183 4595607736439549899906775)
                ·
                  refine ⟨6893411604659324849860163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4595607736439549899906775 6893411604659324849860163)
                  ·
                    refine ⟨10340117406988987274790245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6893411604659324849860163 10340117406988987274790245)
                    ·
                      refine ⟨1938772013810435114023171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10340117406988987274790245 1938772013810435114023171)
                      ·
                        rfl

theorem cell23_3775745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_3775745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775745 prefixEnd_3775745 := by exact prefixLift 3775745
  have htrace : WordTrace (prefixWord ++ tailWord_3775745) baseStart_3775745 baseEnd_3775745 := by
    simpa [prefixWord, tailWord_3775745, baseEnd_3775745] using wordTrace_append hprefix tailTrace_3775745
  have hstable : (prefixWord ++ tailWord_3775745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775745).length < 2 ^ (prefixWord ++ tailWord_3775745).sum := by decide
  have hdescent : baseEnd_3775745 < baseStart_3775745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775755 : List Nat := [1, 1, 1, 1, 5, 5, 1, 2, 2, 4]
def baseStart_3775755 : Nat := 118140960795 + 3775755 * 2 ^ 59
def prefixEnd_3775755 : Nat := 4983230072969 + 3 ^ 40 * 3775755 * 2
def baseEnd_3775755 : Nat := 646259049538993358299375

theorem tailTrace_3775755 : CollatzResearch.WordTrace tailWord_3775755 prefixEnd_3775755 646259049538993358299375 := by
  unfold tailWord_3775755
  simp only [CollatzResearch.WordTrace]
  refine ⟨137713098436091957460168719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91808732290727971640112479 137713098436091957460168719)
  ·
    refine ⟨206569647654137936190253079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137713098436091957460168719 206569647654137936190253079)
    ·
      refine ⟨309854471481206904285379619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206569647654137936190253079 309854471481206904285379619)
      ·
        refine ⟨464781707221810356428069429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309854471481206904285379619 464781707221810356428069429)
        ·
          refine ⟨43573285052044720915131509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 464781707221810356428069429 43573285052044720915131509)
          ·
            refine ⟨4084995473629192585793579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43573285052044720915131509 4084995473629192585793579)
            ·
              refine ⟨6127493210443788878690369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4084995473629192585793579 6127493210443788878690369)
              ·
                refine ⟨4595619907832841659017777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6127493210443788878690369 4595619907832841659017777)
                ·
                  refine ⟨3446714930874631244263333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4595619907832841659017777 3446714930874631244263333)
                  ·
                    refine ⟨646259049538993358299375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3446714930874631244263333 646259049538993358299375)
                    ·
                      rfl

theorem cell23_3775755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 2, 4].length) (baseStart_3775755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775755 prefixEnd_3775755 := by exact prefixLift 3775755
  have htrace : WordTrace (prefixWord ++ tailWord_3775755) baseStart_3775755 baseEnd_3775755 := by
    simpa [prefixWord, tailWord_3775755, baseEnd_3775755] using wordTrace_append hprefix tailTrace_3775755
  have hstable : (prefixWord ++ tailWord_3775755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775755).length < 2 ^ (prefixWord ++ tailWord_3775755).sum := by decide
  have hdescent : baseEnd_3775755 < baseStart_3775755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775775 : List Nat := [1, 1, 2, 4, 4, 2, 1, 1, 1, 2, 4]
def baseStart_3775775 : Nat := 118140960795 + 3775775 * 2 ^ 59
def prefixEnd_3775775 : Nat := 4983230072969 + 3 ^ 40 * 3775775 * 2
def baseEnd_3775775 : Nat := 1938787418230069996648033

theorem tailTrace_3775775 : CollatzResearch.WordTrace tailWord_3775775 prefixEnd_3775775 1938787418230069996648033 := by
  unfold tailWord_3775775
  simp only [CollatzResearch.WordTrace]
  refine ⟨137713827896019500875896779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91809218597346333917264519 137713827896019500875896779)
  ·
    refine ⟨206570741844029251313845169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137713827896019500875896779 206570741844029251313845169)
    ·
      refine ⟨154928056383021938485383877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206570741844029251313845169 154928056383021938485383877)
      ·
        refine ⟨29049010571816613466009477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154928056383021938485383877 29049010571816613466009477)
        ·
          refine ⟨5446689482215615024876777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29049010571816613466009477 5446689482215615024876777)
          ·
            refine ⟨4085017111661711268657583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5446689482215615024876777 4085017111661711268657583)
            ·
              refine ⟨6127525667492566902986375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4085017111661711268657583 6127525667492566902986375)
              ·
                refine ⟨9191288501238850354479563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6127525667492566902986375 9191288501238850354479563)
                ·
                  refine ⟨13786932751858275531719345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9191288501238850354479563 13786932751858275531719345)
                  ·
                    refine ⟨10340199563893706648789509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13786932751858275531719345 10340199563893706648789509)
                    ·
                      refine ⟨1938787418230069996648033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10340199563893706648789509 1938787418230069996648033)
                      ·
                        rfl

theorem cell23_3775775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_3775775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775775 prefixEnd_3775775 := by exact prefixLift 3775775
  have htrace : WordTrace (prefixWord ++ tailWord_3775775) baseStart_3775775 baseEnd_3775775 := by
    simpa [prefixWord, tailWord_3775775, baseEnd_3775775] using wordTrace_append hprefix tailTrace_3775775
  have hstable : (prefixWord ++ tailWord_3775775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775775).length < 2 ^ (prefixWord ++ tailWord_3775775).sum := by decide
  have hdescent : baseEnd_3775775 < baseStart_3775775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775812 : List Nat := [2, 3, 4, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_3775812 : Nat := 118140960795 + 3775812 * 2 ^ 59
def prefixEnd_3775812 : Nat := 4983230072969 + 3 ^ 40 * 3775812 * 2
def baseEnd_3775812 : Nat := 1938806417014286351885363

theorem tailTrace_3775812 : CollatzResearch.WordTrace tailWord_3775812 prefixEnd_3775812 1938806417014286351885363 := by
  unfold tailWord_3775812
  simp only [CollatzResearch.WordTrace]
  refine ⟨68857588698442728097496845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91810118264590304129995793 68857588698442728097496845)
  ·
    refine ⟨25821595761916023036561317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68857588698442728097496845 25821595761916023036561317)
    ·
      refine ⟨4841549205359254319355247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25821595761916023036561317 4841549205359254319355247)
      ·
        refine ⟨7262323808038881479032871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4841549205359254319355247 7262323808038881479032871)
        ·
          refine ⟨10893485712058322218549307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7262323808038881479032871 10893485712058322218549307)
          ·
            refine ⟨16340228568087483327823961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10893485712058322218549307 16340228568087483327823961)
            ·
              refine ⟨12255171426065612495867971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16340228568087483327823961 12255171426065612495867971)
              ·
                refine ⟨18382757139098418743801957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12255171426065612495867971 18382757139098418743801957)
                ·
                  refine ⟨3446766963580953514462867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18382757139098418743801957 3446766963580953514462867)
                  ·
                    refine ⟨5170150445371430271694301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3446766963580953514462867 5170150445371430271694301)
                    ·
                      refine ⟨1938806417014286351885363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5170150445371430271694301 1938806417014286351885363)
                      ·
                        rfl

theorem cell23_3775812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_3775812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775812 prefixEnd_3775812 := by exact prefixLift 3775812
  have htrace : WordTrace (prefixWord ++ tailWord_3775812) baseStart_3775812 baseEnd_3775812 := by
    simpa [prefixWord, tailWord_3775812, baseEnd_3775812] using wordTrace_append hprefix tailTrace_3775812
  have hstable : (prefixWord ++ tailWord_3775812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775812).length < 2 ^ (prefixWord ++ tailWord_3775812).sum := by decide
  have hdescent : baseEnd_3775812 < baseStart_3775812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775829 : List Nat := [1, 3, 2, 2, 3, 3, 2, 1, 2, 1, 3]
def baseStart_3775829 : Nat := 118140960795 + 3775829 * 2 ^ 59
def prefixEnd_3775829 : Nat := 4983230072969 + 3 ^ 40 * 3775829 * 2
def baseEnd_3775829 : Nat := 1938815146185412785372785

theorem tailTrace_3775829 : CollatzResearch.WordTrace tailWord_3775829 prefixEnd_3775829 1938815146185412785372785 := by
  unfold tailWord_3775829
  simp only [CollatzResearch.WordTrace]
  refine ⟨137715797437823868098362541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91810531625215912065575027 137715797437823868098362541)
  ·
    refine ⟨51643424039183950536885953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137715797437823868098362541 51643424039183950536885953)
    ·
      refine ⟨38732568029387962902664465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51643424039183950536885953 38732568029387962902664465)
      ·
        refine ⟨29049426022040972176998349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38732568029387962902664465 29049426022040972176998349)
        ·
          refine ⟨10893534758265364566374381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29049426022040972176998349 10893534758265364566374381)
          ·
            refine ⟨4085075534349511712390393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10893534758265364566374381 4085075534349511712390393)
            ·
              refine ⟨3063806650762133784292795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4085075534349511712390393 3063806650762133784292795)
              ·
                refine ⟨4595709976143200676439193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3063806650762133784292795 4595709976143200676439193)
                ·
                  refine ⟨3446782482107400507329395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4595709976143200676439193 3446782482107400507329395)
                  ·
                    refine ⟨5170173723161100760994093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3446782482107400507329395 5170173723161100760994093)
                    ·
                      refine ⟨1938815146185412785372785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5170173723161100760994093 1938815146185412785372785)
                      ·
                        rfl

theorem cell23_3775829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_3775829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775829 prefixEnd_3775829 := by exact prefixLift 3775829
  have htrace : WordTrace (prefixWord ++ tailWord_3775829) baseStart_3775829 baseEnd_3775829 := by
    simpa [prefixWord, tailWord_3775829, baseEnd_3775829] using wordTrace_append hprefix tailTrace_3775829
  have hstable : (prefixWord ++ tailWord_3775829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775829).length < 2 ^ (prefixWord ++ tailWord_3775829).sum := by decide
  have hdescent : baseEnd_3775829 < baseStart_3775829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775841 : List Nat := [1, 2, 3, 1, 1, 1, 1, 6, 7]
def baseStart_3775841 : Nat := 118140960795 + 3775841 * 2 ^ 59
def prefixEnd_3775841 : Nat := 4983230072969 + 3 ^ 40 * 3775841 * 2
def baseEnd_3775841 : Nat := 215424589772585193158081

theorem tailTrace_3775841 : CollatzResearch.WordTrace tailWord_3775841 prefixEnd_3775841 215424589772585193158081 := by
  unfold tailWord_3775841
  simp only [CollatzResearch.WordTrace]
  refine ⟨137716235113780394147799377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91810823409186929431866251 137716235113780394147799377)
  ·
    refine ⟨103287176335335295610849533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137716235113780394147799377 103287176335335295610849533)
    ·
      refine ⟨38732691125750735854068575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103287176335335295610849533 38732691125750735854068575)
      ·
        refine ⟨58099036688626103781102863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38732691125750735854068575 58099036688626103781102863)
        ·
          refine ⟨87148555032939155671654295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58099036688626103781102863 87148555032939155671654295)
          ·
            refine ⟨130722832549408733507481443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87148555032939155671654295 130722832549408733507481443)
            ·
              refine ⟨196084248824113100261222165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130722832549408733507481443 196084248824113100261222165)
              ·
                refine ⟨9191449163630301574744789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 196084248824113100261222165 9191449163630301574744789)
                ·
                  refine ⟨215424589772585193158081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9191449163630301574744789 215424589772585193158081)
                  ·
                    rfl

theorem cell23_3775841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 7].length) (baseStart_3775841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775841 prefixEnd_3775841 := by exact prefixLift 3775841
  have htrace : WordTrace (prefixWord ++ tailWord_3775841) baseStart_3775841 baseEnd_3775841 := by
    simpa [prefixWord, tailWord_3775841, baseEnd_3775841] using wordTrace_append hprefix tailTrace_3775841
  have hstable : (prefixWord ++ tailWord_3775841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775841).length < 2 ^ (prefixWord ++ tailWord_3775841).sum := by decide
  have hdescent : baseEnd_3775841 < baseStart_3775841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775868 : List Nat := [2, 2, 2, 1, 1, 1, 4, 2, 2, 3, 3]
def baseStart_3775868 : Nat := 118140960795 + 3775868 * 2 ^ 59
def prefixEnd_3775868 : Nat := 4983230072969 + 3 ^ 40 * 3775868 * 2
def baseEnd_3775868 : Nat := 1938835171930938132785105

theorem tailTrace_3775868 : CollatzResearch.WordTrace tailWord_3775868 prefixEnd_3775868 1938835171930938132785105 := by
  unfold tailWord_3775868
  simp only [CollatzResearch.WordTrace]
  refine ⟨68858609942341288879516129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91811479923121718506021505 68858609942341288879516129)
  ·
    refine ⟨51643957456755966659637097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68858609942341288879516129 51643957456755966659637097)
    ·
      refine ⟨38732968092566974994727823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51643957456755966659637097 38732968092566974994727823)
      ·
        refine ⟨58099452138850462492091735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38732968092566974994727823 58099452138850462492091735)
        ·
          refine ⟨87149178208275693738137603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58099452138850462492091735 87149178208275693738137603)
          ·
            refine ⟨130723767312413540607206405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87149178208275693738137603 130723767312413540607206405)
            ·
              refine ⟨24510706371077538863851201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130723767312413540607206405 24510706371077538863851201)
              ·
                refine ⟨18383029778308154147888401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24510706371077538863851201 18383029778308154147888401)
                ·
                  refine ⟨13787272333731115610916301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18383029778308154147888401 13787272333731115610916301)
                  ·
                    refine ⟨5170227125149168354093613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13787272333731115610916301 5170227125149168354093613)
                    ·
                      refine ⟨1938835171930938132785105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5170227125149168354093613 1938835171930938132785105)
                      ·
                        rfl

theorem cell23_3775868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_3775868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775868 prefixEnd_3775868 := by exact prefixLift 3775868
  have htrace : WordTrace (prefixWord ++ tailWord_3775868) baseStart_3775868 baseEnd_3775868 := by
    simpa [prefixWord, tailWord_3775868, baseEnd_3775868] using wordTrace_append hprefix tailTrace_3775868
  have hstable : (prefixWord ++ tailWord_3775868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775868).length < 2 ^ (prefixWord ++ tailWord_3775868).sum := by decide
  have hdescent : baseEnd_3775868 < baseStart_3775868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775875 : List Nat := [1, 1, 1, 3, 5, 2, 1, 4, 5]
def baseStart_3775875 : Nat := 118140960795 + 3775875 * 2 ^ 59
def prefixEnd_3775875 : Nat := 4983230072969 + 3 ^ 40 * 3775875 * 2
def baseEnd_3775875 : Nat := 215426529588391067266397

theorem tailTrace_3775875 : CollatzResearch.WordTrace tailWord_3775875 prefixEnd_3775875 215426529588391067266397 := by
  unfold tailWord_3775875
  simp only [CollatzResearch.WordTrace]
  refine ⟨137717475195657217954537079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91811650130438145303024719 137717475195657217954537079)
  ·
    refine ⟨206576212793485826931805619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137717475195657217954537079 206576212793485826931805619)
    ·
      refine ⟨309864319190228740397708429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206576212793485826931805619 309864319190228740397708429)
      ·
        refine ⟨116199119696335777649140661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309864319190228740397708429 116199119696335777649140661)
        ·
          refine ⟨10893667471531479154606937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116199119696335777649140661 10893667471531479154606937)
          ·
            refine ⟨8170250603648609365955203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10893667471531479154606937 8170250603648609365955203)
            ·
              refine ⟨12255375905472914048932805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8170250603648609365955203 12255375905472914048932805)
              ·
                refine ⟨2297882982276171384174901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12255375905472914048932805 2297882982276171384174901)
                ·
                  refine ⟨215426529588391067266397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2297882982276171384174901 215426529588391067266397)
                  ·
                    rfl

theorem cell23_3775875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 4, 5].length) (baseStart_3775875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775875 prefixEnd_3775875 := by exact prefixLift 3775875
  have htrace : WordTrace (prefixWord ++ tailWord_3775875) baseStart_3775875 baseEnd_3775875 := by
    simpa [prefixWord, tailWord_3775875, baseEnd_3775875] using wordTrace_append hprefix tailTrace_3775875
  have hstable : (prefixWord ++ tailWord_3775875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775875).length < 2 ^ (prefixWord ++ tailWord_3775875).sum := by decide
  have hdescent : baseEnd_3775875 < baseStart_3775875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775969 : List Nat := [1, 2, 3, 1, 2, 5, 1, 3, 1, 4]
def baseStart_3775969 : Nat := 118140960795 + 3775969 * 2 ^ 59
def prefixEnd_3775969 : Nat := 4983230072969 + 3 ^ 40 * 3775969 * 2
def baseEnd_3775969 : Nat := 646295677825680745874047

theorem tailTrace_3775969 : CollatzResearch.WordTrace tailWord_3775969 prefixEnd_3775969 646295677825680745874047 := by
  unfold tailWord_3775969
  simp only [CollatzResearch.WordTrace]
  refine ⟨137720903657316672008458961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91813935771544448005639307 137720903657316672008458961)
  ·
    refine ⟨103290677742987504006344221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137720903657316672008458961 103290677742987504006344221)
    ·
      refine ⟨38734004153620314002379083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103290677742987504006344221 38734004153620314002379083)
      ·
        refine ⟨58101006230430471003568625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38734004153620314002379083 58101006230430471003568625)
        ·
          refine ⟨43575754672822853252676469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58101006230430471003568625 43575754672822853252676469)
          ·
            refine ⟨4085227000577142492438419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43575754672822853252676469 4085227000577142492438419)
            ·
              refine ⟨6127840500865713738657629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4085227000577142492438419 6127840500865713738657629)
              ·
                refine ⟨2297940187824642651996611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6127840500865713738657629 2297940187824642651996611)
                ·
                  refine ⟨3446910281736963977994917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2297940187824642651996611 3446910281736963977994917)
                  ·
                    refine ⟨646295677825680745874047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3446910281736963977994917 646295677825680745874047)
                    ·
                      rfl

theorem cell23_3775969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 3, 1, 4].length) (baseStart_3775969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775969 prefixEnd_3775969 := by exact prefixLift 3775969
  have htrace : WordTrace (prefixWord ++ tailWord_3775969) baseStart_3775969 baseEnd_3775969 := by
    simpa [prefixWord, tailWord_3775969, baseEnd_3775969] using wordTrace_append hprefix tailTrace_3775969
  have hstable : (prefixWord ++ tailWord_3775969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775969).length < 2 ^ (prefixWord ++ tailWord_3775969).sum := by decide
  have hdescent : baseEnd_3775969 < baseStart_3775969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775986 : List Nat := [3, 2, 1, 4, 1, 2, 3, 2, 1, 4]
def baseStart_3775986 : Nat := 118140960795 + 3775986 * 2 ^ 59
def prefixEnd_3775986 : Nat := 4983230072969 + 3 ^ 40 * 3775986 * 2
def baseEnd_3775986 : Nat := 646298587549389557036521

theorem tailTrace_3775986 : CollatzResearch.WordTrace tailWord_3775986 prefixEnd_3775986 646298587549389557036521 := by
  unfold tailWord_3775986
  simp only [CollatzResearch.WordTrace]
  refine ⟨34430380924563770977956953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91814349132170055941218541 34430380924563770977956953)
  ·
    refine ⟨25822785693422828233467715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34430380924563770977956953 25822785693422828233467715)
    ·
      refine ⟨38734178540134242350201573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25822785693422828233467715 38734178540134242350201573)
      ·
        refine ⟨7262658476275170440662795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38734178540134242350201573 7262658476275170440662795)
        ·
          refine ⟨10893987714412755660994193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7262658476275170440662795 10893987714412755660994193)
          ·
            refine ⟨8170490785809566745745645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10893987714412755660994193 8170490785809566745745645)
            ·
              refine ⟨3063934044678587529654617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8170490785809566745745645 3063934044678587529654617)
              ·
                refine ⟨2297950533508940647240963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3063934044678587529654617 2297950533508940647240963)
                ·
                  refine ⟨3446925800263410970861445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2297950533508940647240963 3446925800263410970861445)
                  ·
                    refine ⟨646298587549389557036521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3446925800263410970861445 646298587549389557036521)
                    ·
                      rfl

theorem cell23_3775986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 2, 1, 4].length) (baseStart_3775986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775986 prefixEnd_3775986 := by exact prefixLift 3775986
  have htrace : WordTrace (prefixWord ++ tailWord_3775986) baseStart_3775986 baseEnd_3775986 := by
    simpa [prefixWord, tailWord_3775986, baseEnd_3775986] using wordTrace_append hprefix tailTrace_3775986
  have hstable : (prefixWord ++ tailWord_3775986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775986).length < 2 ^ (prefixWord ++ tailWord_3775986).sum := by decide
  have hdescent : baseEnd_3775986 < baseStart_3775986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3775992 : List Nat := [2, 1, 2, 1, 1, 5, 3, 1, 3, 1, 3]
def baseStart_3775992 : Nat := 118140960795 + 3775992 * 2 ^ 59
def prefixEnd_3775992 : Nat := 4983230072969 + 3 ^ 40 * 3775992 * 2
def baseEnd_3775992 : Nat := 1938898843532095647634535

theorem tailTrace_3775992 : CollatzResearch.WordTrace tailWord_3775992 prefixEnd_3775992 1938898843532095647634535 := by
  unfold tailWord_3775992
  simp only [CollatzResearch.WordTrace]
  refine ⟨68860871268116673468273115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91814495024155564624364153 68860871268116673468273115)
  ·
    refine ⟨103291306902175010202409673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68860871268116673468273115 103291306902175010202409673)
    ·
      refine ⟨77468480176631257651807255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103291306902175010202409673 77468480176631257651807255)
      ·
        refine ⟨116202720264946886477710883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77468480176631257651807255 116202720264946886477710883)
        ·
          refine ⟨174304080397420329716566325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116202720264946886477710883 174304080397420329716566325)
          ·
            refine ⟨16341007537258155910928093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 174304080397420329716566325 16341007537258155910928093)
            ·
              refine ⟨6127877826471808466598035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16341007537258155910928093 6127877826471808466598035)
              ·
                refine ⟨9191816739707712699897053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6127877826471808466598035 9191816739707712699897053)
                ·
                  refine ⟨3446931277390392262461395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9191816739707712699897053 3446931277390392262461395)
                  ·
                    refine ⟨5170396916085588393692093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3446931277390392262461395 5170396916085588393692093)
                    ·
                      refine ⟨1938898843532095647634535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5170396916085588393692093 1938898843532095647634535)
                      ·
                        rfl

theorem cell23_3775992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 3, 1, 3].length) (baseStart_3775992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3775992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3775992 prefixEnd_3775992 := by exact prefixLift 3775992
  have htrace : WordTrace (prefixWord ++ tailWord_3775992) baseStart_3775992 baseEnd_3775992 := by
    simpa [prefixWord, tailWord_3775992, baseEnd_3775992] using wordTrace_append hprefix tailTrace_3775992
  have hstable : (prefixWord ++ tailWord_3775992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3775992).length < 2 ^ (prefixWord ++ tailWord_3775992).sum := by decide
  have hdescent : baseEnd_3775992 < baseStart_3775992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3775992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776055 : List Nat := [1, 1, 3, 1, 2, 6, 1, 8]
def baseStart_3776055 : Nat := 118140960795 + 3776055 * 2 ^ 59
def prefixEnd_3776055 : Nat := 4983230072969 + 3 ^ 40 * 3776055 * 2
def baseEnd_3776055 : Nat := 71812266400493663005435

theorem tailTrace_3776055 : CollatzResearch.WordTrace tailWord_3776055 prefixEnd_3776055 71812266400493663005435 := by
  unfold tailWord_3776055
  simp only [CollatzResearch.WordTrace]
  refine ⟨137724040335005108696089619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91816026890003405797393079 137724040335005108696089619)
  ·
    refine ⟨206586060502507663044134429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137724040335005108696089619 206586060502507663044134429)
    ·
      refine ⟨77469772688440373641550411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206586060502507663044134429 77469772688440373641550411)
      ·
        refine ⟨116204659032660560462325617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77469772688440373641550411 116204659032660560462325617)
        ·
          refine ⟨87153494274495420346744213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116204659032660560462325617 87153494274495420346744213)
          ·
            refine ⟨4085320044116972828753635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 87153494274495420346744213 4085320044116972828753635)
            ·
              refine ⟨6127980066175459243130453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4085320044116972828753635 6127980066175459243130453)
              ·
                refine ⟨71812266400493663005435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6127980066175459243130453 71812266400493663005435)
                ·
                  rfl

theorem cell23_3776055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 8].length) (baseStart_3776055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776055 prefixEnd_3776055 := by exact prefixLift 3776055
  have htrace : WordTrace (prefixWord ++ tailWord_3776055) baseStart_3776055 baseEnd_3776055 := by
    simpa [prefixWord, tailWord_3776055, baseEnd_3776055] using wordTrace_append hprefix tailTrace_3776055
  have hstable : (prefixWord ++ tailWord_3776055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776055).length < 2 ^ (prefixWord ++ tailWord_3776055).sum := by decide
  have hdescent : baseEnd_3776055 < baseStart_3776055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776070 : List Nat := [6, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2]
def baseStart_3776070 : Nat := 118140960795 + 3776070 * 2 ^ 59
def prefixEnd_3776070 : Nat := 4983230072969 + 3 ^ 40 * 3776070 * 2
def baseEnd_3776070 : Nat := 1938938895023146342459177

theorem tailTrace_3776070 : CollatzResearch.WordTrace tailWord_3776070 prefixEnd_3776070 1938938895023146342459177 := by
  unfold tailWord_3776070
  simp only [CollatzResearch.WordTrace]
  refine ⟨4303893357185961445558927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 91816391619967177505257109 4303893357185961445558927)
  ·
    refine ⟨6455840035778942168338391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4303893357185961445558927 6455840035778942168338391)
    ·
      refine ⟨9683760053668413252507587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6455840035778942168338391 9683760053668413252507587)
      ·
        refine ⟨14525640080502619878761381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9683760053668413252507587 14525640080502619878761381)
        ·
          refine ⟨2723557515094241227267759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14525640080502619878761381 2723557515094241227267759)
          ·
            refine ⟨4085336272641361840901639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2723557515094241227267759 4085336272641361840901639)
            ·
              refine ⟨6128004408962042761352459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4085336272641361840901639 6128004408962042761352459)
              ·
                refine ⟨9192006613443064142028689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6128004408962042761352459 9192006613443064142028689)
                ·
                  refine ⟨6894004960082298106521517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9192006613443064142028689 6894004960082298106521517)
                  ·
                    refine ⟨2585251860030861789945569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6894004960082298106521517 2585251860030861789945569)
                    ·
                      refine ⟨1938938895023146342459177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2585251860030861789945569 1938938895023146342459177)
                      ·
                        rfl

theorem cell23_3776070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_3776070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776070 prefixEnd_3776070 := by exact prefixLift 3776070
  have htrace : WordTrace (prefixWord ++ tailWord_3776070) baseStart_3776070 baseEnd_3776070 := by
    simpa [prefixWord, tailWord_3776070, baseEnd_3776070] using wordTrace_append hprefix tailTrace_3776070
  have hstable : (prefixWord ++ tailWord_3776070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776070).length < 2 ^ (prefixWord ++ tailWord_3776070).sum := by decide
  have hdescent : baseEnd_3776070 < baseStart_3776070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776082 : List Nat := [3, 2, 2, 1, 2, 2, 2, 2, 1, 3, 3]
def baseStart_3776082 : Nat := 118140960795 + 3776082 * 2 ^ 59
def prefixEnd_3776082 : Nat := 4983230072969 + 3 ^ 40 * 3776082 * 2
def baseEnd_3776082 : Nat := 1938945056791000295509121

theorem tailTrace_3776082 : CollatzResearch.WordTrace tailWord_3776082 prefixEnd_3776082 1938945056791000295509121 := by
  unfold tailWord_3776082
  simp only [CollatzResearch.WordTrace]
  refine ⟨34431256276476823076830625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91816683403938194871548333 34431256276476823076830625)
  ·
    refine ⟨25823442207357617307622969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34431256276476823076830625 25823442207357617307622969)
    ·
      refine ⟨19367581655518212980717227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25823442207357617307622969 19367581655518212980717227)
      ·
        refine ⟨29051372483277319471075841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19367581655518212980717227 29051372483277319471075841)
        ·
          refine ⟨21788529362457989603306881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29051372483277319471075841 21788529362457989603306881)
          ·
            refine ⟨16341397021843492202480161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21788529362457989603306881 16341397021843492202480161)
            ·
              refine ⟨12256047766382619151860121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16341397021843492202480161 12256047766382619151860121)
              ·
                refine ⟨9192035824786964363895091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12256047766382619151860121 9192035824786964363895091)
                ·
                  refine ⟨13788053737180446545842637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9192035824786964363895091 13788053737180446545842637)
                  ·
                    refine ⟨5170520151442667454690989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13788053737180446545842637 5170520151442667454690989)
                    ·
                      refine ⟨1938945056791000295509121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5170520151442667454690989 1938945056791000295509121)
                      ·
                        rfl

theorem cell23_3776082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_3776082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776082 prefixEnd_3776082 := by exact prefixLift 3776082
  have htrace : WordTrace (prefixWord ++ tailWord_3776082) baseStart_3776082 baseEnd_3776082 := by
    simpa [prefixWord, tailWord_3776082, baseEnd_3776082] using wordTrace_append hprefix tailTrace_3776082
  have hstable : (prefixWord ++ tailWord_3776082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776082).length < 2 ^ (prefixWord ++ tailWord_3776082).sum := by decide
  have hdescent : baseEnd_3776082 < baseStart_3776082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776093 : List Nat := [1, 4, 4, 2, 1, 2, 1, 2, 2, 4]
def baseStart_3776093 : Nat := 118140960795 + 3776093 * 2 ^ 59
def prefixEnd_3776093 : Nat := 4983230072969 + 3 ^ 40 * 3776093 * 2
def baseEnd_3776093 : Nat := 646316901692733250823857

theorem tailTrace_3776093 : CollatzResearch.WordTrace tailWord_3776093 prefixEnd_3776093 646316901692733250823857 := by
  unfold tailWord_3776093
  simp only [CollatzResearch.WordTrace]
  refine ⟨137725426308867441185972933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91816950872578294123981955 137725426308867441185972933)
  ·
    refine ⟨25823517432912645222369925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137725426308867441185972933 25823517432912645222369925)
    ·
      refine ⟨4841909518671120979194361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25823517432912645222369925 4841909518671120979194361)
      ·
        refine ⟨3631432139003340734395771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4841909518671120979194361 3631432139003340734395771)
        ·
          refine ⟨5447148208505011101593657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3631432139003340734395771 5447148208505011101593657)
          ·
            refine ⟨4085361156378758326195243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5447148208505011101593657 4085361156378758326195243)
            ·
              refine ⟨6128041734568137489292865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4085361156378758326195243 6128041734568137489292865)
              ·
                refine ⟨4596031300926103116969649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6128041734568137489292865 4596031300926103116969649)
                ·
                  refine ⟨3447023475694577337727237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4596031300926103116969649 3447023475694577337727237)
                  ·
                    refine ⟨646316901692733250823857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3447023475694577337727237 646316901692733250823857)
                    ·
                      rfl

theorem cell23_3776093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_3776093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776093 prefixEnd_3776093 := by exact prefixLift 3776093
  have htrace : WordTrace (prefixWord ++ tailWord_3776093) baseStart_3776093 baseEnd_3776093 := by
    simpa [prefixWord, tailWord_3776093, baseEnd_3776093] using wordTrace_append hprefix tailTrace_3776093
  have hstable : (prefixWord ++ tailWord_3776093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776093).length < 2 ^ (prefixWord ++ tailWord_3776093).sum := by decide
  have hdescent : baseEnd_3776093 < baseStart_3776093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776099 : List Nat := [1, 1, 1, 5, 1, 3, 3, 2, 2, 1, 3]
def baseStart_3776099 : Nat := 118140960795 + 3776099 * 2 ^ 59
def prefixEnd_3776099 : Nat := 4983230072969 + 3 ^ 40 * 3776099 * 2
def baseEnd_3776099 : Nat := 1938953785962126728996543

theorem tailTrace_3776099 : CollatzResearch.WordTrace tailWord_3776099 prefixEnd_3776099 1938953785962126728996543 := by
  unfold tailWord_3776099
  simp only [CollatzResearch.WordTrace]
  refine ⟨137725645146845704210691351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91817096764563802807127567 137725645146845704210691351)
  ·
    refine ⟨206588467720268556316037027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137725645146845704210691351 206588467720268556316037027)
    ·
      refine ⟨309882701580402834474055541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206588467720268556316037027 309882701580402834474055541)
      ·
        refine ⟨29051503273162765731942707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 309882701580402834474055541 29051503273162765731942707)
        ·
          refine ⟨43577254909744148597914061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29051503273162765731942707 43577254909744148597914061)
          ·
            refine ⟨16341470591154055724217773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43577254909744148597914061 16341470591154055724217773)
            ·
              refine ⟨6128051471682770896581665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16341470591154055724217773 6128051471682770896581665)
              ·
                refine ⟨4596038603762078172436249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6128051471682770896581665 4596038603762078172436249)
                ·
                  refine ⟨3447028952821558629327187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4596038603762078172436249 3447028952821558629327187)
                  ·
                    refine ⟨5170543429232337943990781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3447028952821558629327187 5170543429232337943990781)
                    ·
                      refine ⟨1938953785962126728996543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5170543429232337943990781 1938953785962126728996543)
                      ·
                        rfl

theorem cell23_3776099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_3776099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776099 prefixEnd_3776099 := by exact prefixLift 3776099
  have htrace : WordTrace (prefixWord ++ tailWord_3776099) baseStart_3776099 baseEnd_3776099 := by
    simpa [prefixWord, tailWord_3776099, baseEnd_3776099] using wordTrace_append hprefix tailTrace_3776099
  have hstable : (prefixWord ++ tailWord_3776099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776099).length < 2 ^ (prefixWord ++ tailWord_3776099).sum := by decide
  have hdescent : baseEnd_3776099 < baseStart_3776099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776122 : List Nat := [3, 1, 1, 1, 1, 1, 1, 7, 1, 4, 2]
def baseStart_3776122 : Nat := 118140960795 + 3776122 * 2 ^ 59
def prefixEnd_3776122 : Nat := 4983230072969 + 3 ^ 40 * 3776122 * 2
def baseEnd_3776122 : Nat := 1938965596017180139008937

theorem tailTrace_3776122 : CollatzResearch.WordTrace tailWord_3776122 prefixEnd_3776122 1938965596017180139008937 := by
  unfold tailWord_3776122
  simp only [CollatzResearch.WordTrace]
  refine ⟨34431621006440594784694655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91817656017174919425852413 34431621006440594784694655)
  ·
    refine ⟨51647431509660892177041983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34431621006440594784694655 51647431509660892177041983)
    ·
      refine ⟨77471147264491338265562975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51647431509660892177041983 77471147264491338265562975)
      ·
        refine ⟨116206720896737007398344463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77471147264491338265562975 116206720896737007398344463)
        ·
          refine ⟨174310081345105511097516695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116206720896737007398344463 174310081345105511097516695)
          ·
            refine ⟨261465122017658266646275043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174310081345105511097516695 261465122017658266646275043)
            ·
              refine ⟨392197683026487399969412565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261465122017658266646275043 392197683026487399969412565)
              ·
                refine ⟨9192133195933298436783107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 392197683026487399969412565 9192133195933298436783107)
                ·
                  refine ⟨13788199793899947655174661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9192133195933298436783107 13788199793899947655174661)
                  ·
                    refine ⟨2585287461356240185345249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13788199793899947655174661 2585287461356240185345249)
                    ·
                      refine ⟨1938965596017180139008937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2585287461356240185345249 1938965596017180139008937)
                      ·
                        rfl

theorem cell23_3776122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 1, 4, 2].length) (baseStart_3776122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776122 prefixEnd_3776122 := by exact prefixLift 3776122
  have htrace : WordTrace (prefixWord ++ tailWord_3776122) baseStart_3776122 baseEnd_3776122 := by
    simpa [prefixWord, tailWord_3776122, baseEnd_3776122] using wordTrace_append hprefix tailTrace_3776122
  have hstable : (prefixWord ++ tailWord_3776122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776122).length < 2 ^ (prefixWord ++ tailWord_3776122).sum := by decide
  have hdescent : baseEnd_3776122 < baseStart_3776122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776142 : List Nat := [4, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5]
def baseStart_3776142 : Nat := 118140960795 + 3776142 * 2 ^ 59
def prefixEnd_3776142 : Nat := 4983230072969 + 3 ^ 40 * 3776142 * 2
def baseEnd_3776142 : Nat := 1938975865630270060758845

theorem tailTrace_3776142 : CollatzResearch.WordTrace tailWord_3776142 prefixEnd_3776142 1938975865630270060758845 := by
  unfold tailWord_3776142
  simp only [CollatzResearch.WordTrace]
  refine ⟨17215901685711240319313335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91818142323793281703004453 17215901685711240319313335)
  ·
    refine ⟨25823852528566860478970003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17215901685711240319313335 25823852528566860478970003)
    ·
      refine ⟨38735778792850290718455005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25823852528566860478970003 38735778792850290718455005)
      ·
        refine ⟨14525917047318859019420627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38735778792850290718455005 14525917047318859019420627)
        ·
          refine ⟨21788875570978288529130941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14525917047318859019420627 21788875570978288529130941)
          ·
            refine ⟨8170828339116858198424103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21788875570978288529130941 8170828339116858198424103)
            ·
              refine ⟨12256242508675287297636155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8170828339116858198424103 12256242508675287297636155)
              ·
                refine ⟨18384363763012930946454233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12256242508675287297636155 18384363763012930946454233)
                ·
                  refine ⟨13788272822259698209840675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18384363763012930946454233 13788272822259698209840675)
                  ·
                    refine ⟨20682409233389547314761013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13788272822259698209840675 20682409233389547314761013)
                    ·
                      refine ⟨1938975865630270060758845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20682409233389547314761013 1938975865630270060758845)
                      ·
                        rfl

theorem cell23_3776142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_3776142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776142 prefixEnd_3776142 := by exact prefixLift 3776142
  have htrace : WordTrace (prefixWord ++ tailWord_3776142) baseStart_3776142 baseEnd_3776142 := by
    simpa [prefixWord, tailWord_3776142, baseEnd_3776142] using wordTrace_append hprefix tailTrace_3776142
  have hstable : (prefixWord ++ tailWord_3776142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776142).length < 2 ^ (prefixWord ++ tailWord_3776142).sum := by decide
  have hdescent : baseEnd_3776142 < baseStart_3776142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776175 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 4, 5]
def baseStart_3776175 : Nat := 118140960795 + 3776175 * 2 ^ 59
def prefixEnd_3776175 : Nat := 4983230072969 + 3 ^ 40 * 3776175 * 2
def baseEnd_3776175 : Nat := 646330936830622810548731

theorem tailTrace_3776175 : CollatzResearch.WordTrace tailWord_3776175 prefixEnd_3776175 646330936830622810548731 := by
  unfold tailWord_3776175
  simp only [CollatzResearch.WordTrace]
  refine ⟨137728417094570369190457979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91818944729713579460305319 137728417094570369190457979)
  ·
    refine ⟨206592625641855553785686969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137728417094570369190457979 206592625641855553785686969)
    ·
      refine ⟨154944469231391665339265227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206592625641855553785686969 154944469231391665339265227)
      ·
        refine ⟨232416703847087498008897841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154944469231391665339265227 232416703847087498008897841)
        ·
          refine ⟨174312527885315623506673381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232416703847087498008897841 174312527885315623506673381)
          ·
            refine ⟨32683598978496679407501259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174312527885315623506673381 32683598978496679407501259)
            ·
              refine ⟨49025398467745019111251889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32683598978496679407501259 49025398467745019111251889)
              ·
                refine ⟨36769048850808764333438917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49025398467745019111251889 36769048850808764333438917)
                ·
                  refine ⟨6894196659526643312519797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36769048850808764333438917 6894196659526643312519797)
                  ·
                    refine ⟨646330936830622810548731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6894196659526643312519797 646330936830622810548731)
                    ·
                      rfl

theorem cell23_3776175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 5].length) (baseStart_3776175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776175 prefixEnd_3776175 := by exact prefixLift 3776175
  have htrace : WordTrace (prefixWord ++ tailWord_3776175) baseStart_3776175 baseEnd_3776175 := by
    simpa [prefixWord, tailWord_3776175, baseEnd_3776175] using wordTrace_append hprefix tailTrace_3776175
  have hstable : (prefixWord ++ tailWord_3776175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776175).length < 2 ^ (prefixWord ++ tailWord_3776175).sum := by decide
  have hdescent : baseEnd_3776175 < baseStart_3776175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776192 : List Nat := [2, 1, 1, 2, 4, 1, 4, 1, 2, 5]
def baseStart_3776192 : Nat := 118140960795 + 3776192 * 2 ^ 59
def prefixEnd_3776192 : Nat := 4983230072969 + 3 ^ 40 * 3776192 * 2
def baseEnd_3776192 : Nat := 646333846554331621711205

theorem tailTrace_3776192 : CollatzResearch.WordTrace tailWord_3776192 prefixEnd_3776192 646333846554331621711205 := by
  unfold tailWord_3776192
  simp only [CollatzResearch.WordTrace]
  refine ⟨68864518567754390546913415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91819358090339187395884553 68864518567754390546913415)
  ·
    refine ⟨103296777851631585820370123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68864518567754390546913415 103296777851631585820370123)
    ·
      refine ⟨154945166777447378730555185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103296777851631585820370123 154945166777447378730555185)
      ·
        refine ⟨116208875083085534047916389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154945166777447378730555185 116208875083085534047916389)
        ·
          refine ⟨21789164078078537633984323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116208875083085534047916389 21789164078078537633984323)
          ·
            refine ⟨32683746117117806450976485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21789164078078537633984323 32683746117117806450976485)
            ·
              refine ⟨6128202396959588709558091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32683746117117806450976485 6128202396959588709558091)
              ·
                refine ⟨9192303595439383064337137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6128202396959588709558091 9192303595439383064337137)
                ·
                  refine ⟨6894227696579537298252853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9192303595439383064337137 6894227696579537298252853)
                  ·
                    refine ⟨646333846554331621711205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6894227696579537298252853 646333846554331621711205)
                    ·
                      rfl

theorem cell23_3776192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 2, 5].length) (baseStart_3776192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776192 prefixEnd_3776192 := by exact prefixLift 3776192
  have htrace : WordTrace (prefixWord ++ tailWord_3776192) baseStart_3776192 baseEnd_3776192 := by
    simpa [prefixWord, tailWord_3776192, baseEnd_3776192] using wordTrace_append hprefix tailTrace_3776192
  have hstable : (prefixWord ++ tailWord_3776192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776192).length < 2 ^ (prefixWord ++ tailWord_3776192).sum := by decide
  have hdescent : baseEnd_3776192 < baseStart_3776192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776215 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 5]
def baseStart_3776215 : Nat := 118140960795 + 3776215 * 2 ^ 59
def prefixEnd_3776215 : Nat := 4983230072969 + 3 ^ 40 * 3776215 * 2
def baseEnd_3776215 : Nat := 1939013349718048275146009

theorem tailTrace_3776215 : CollatzResearch.WordTrace tailWord_3776215 prefixEnd_3776215 1939013349718048275146009 := by
  unfold tailWord_3776215
  simp only [CollatzResearch.WordTrace]
  refine ⟨137729876014425456021914099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91819917342950304014609399 137729876014425456021914099)
  ·
    refine ⟨206594814021638184032871149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137729876014425456021914099 206594814021638184032871149)
    ·
      refine ⟨77473055258114319012326681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206594814021638184032871149 77473055258114319012326681)
      ·
        refine ⟨58104791443585739259245011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77473055258114319012326681 58104791443585739259245011)
        ·
          refine ⟨87157187165378608888867517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58104791443585739259245011 87157187165378608888867517)
          ·
            refine ⟨32683945187016978333325319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87157187165378608888867517 32683945187016978333325319)
            ·
              refine ⟨49025917780525467499987979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32683945187016978333325319 49025917780525467499987979)
              ·
                refine ⟨73538876670788201249981969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49025917780525467499987979 73538876670788201249981969)
                ·
                  refine ⟨55154157503091150937486477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73538876670788201249981969 55154157503091150937486477)
                  ·
                    refine ⟨20682809063659181601557429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55154157503091150937486477 20682809063659181601557429)
                    ·
                      refine ⟨1939013349718048275146009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20682809063659181601557429 1939013349718048275146009)
                      ·
                        rfl

theorem cell23_3776215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_3776215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776215 prefixEnd_3776215 := by exact prefixLift 3776215
  have htrace : WordTrace (prefixWord ++ tailWord_3776215) baseStart_3776215 baseEnd_3776215 := by
    simpa [prefixWord, tailWord_3776215, baseEnd_3776215] using wordTrace_append hprefix tailTrace_3776215
  have hstable : (prefixWord ++ tailWord_3776215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776215).length < 2 ^ (prefixWord ++ tailWord_3776215).sum := by decide
  have hdescent : baseEnd_3776215 < baseStart_3776215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776229 : List Nat := [1, 3, 1, 4, 1, 1, 3, 1, 2, 4, 2]
def baseStart_3776229 : Nat := 118140960795 + 3776229 * 2 ^ 59
def prefixEnd_3776229 : Nat := 4983230072969 + 3 ^ 40 * 3776229 * 2
def baseEnd_3776229 : Nat := 1939020538447211220370945

theorem tailTrace_3776229 : CollatzResearch.WordTrace tailWord_3776229 prefixEnd_3776229 1939020538447211220370945 := by
  unfold tailWord_3776229
  simp only [CollatzResearch.WordTrace]
  refine ⟨137730386636374736412923741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91820257757583157608615827 137730386636374736412923741)
  ·
    refine ⟨51648894988640526154846403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137730386636374736412923741 51648894988640526154846403)
    ·
      refine ⟨77473342482960789232269605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51648894988640526154846403 77473342482960789232269605)
      ·
        refine ⟨14526251715555147981050551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77473342482960789232269605 14526251715555147981050551)
        ·
          refine ⟨21789377573332721971575827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14526251715555147981050551 21789377573332721971575827)
          ·
            refine ⟨32684066359999082957363741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21789377573332721971575827 32684066359999082957363741)
            ·
              refine ⟨12256524884999656109011403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32684066359999082957363741 12256524884999656109011403)
              ·
                refine ⟨18384787327499484163517105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12256524884999656109011403 18384787327499484163517105)
                ·
                  refine ⟨13788590495624613122637829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18384787327499484163517105 13788590495624613122637829)
                  ·
                    refine ⟨2585360717929614960494593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13788590495624613122637829 2585360717929614960494593)
                    ·
                      refine ⟨1939020538447211220370945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2585360717929614960494593 1939020538447211220370945)
                      ·
                        rfl

theorem cell23_3776229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_3776229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776229 prefixEnd_3776229 := by exact prefixLift 3776229
  have htrace : WordTrace (prefixWord ++ tailWord_3776229) baseStart_3776229 baseEnd_3776229 := by
    simpa [prefixWord, tailWord_3776229, baseEnd_3776229] using wordTrace_append hprefix tailTrace_3776229
  have hstable : (prefixWord ++ tailWord_3776229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776229).length < 2 ^ (prefixWord ++ tailWord_3776229).sum := by decide
  have hdescent : baseEnd_3776229 < baseStart_3776229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776246 : List Nat := [5, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4]
def baseStart_3776246 : Nat := 118140960795 + 3776246 * 2 ^ 59
def prefixEnd_3776246 : Nat := 4983230072969 + 3 ^ 40 * 3776246 * 2
def baseEnd_3776246 : Nat := 1939029267618337653858367

theorem tailTrace_3776246 : CollatzResearch.WordTrace tailWord_3776246 prefixEnd_3776246 1939029267618337653858367 := by
  unfold tailWord_3776246
  simp only [CollatzResearch.WordTrace]
  refine ⟨8608187917332071769768287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91820671118208765544195061 8608187917332071769768287)
  ·
    refine ⟨12912281875998107654652431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8608187917332071769768287 12912281875998107654652431)
    ·
      refine ⟨19368422813997161481978647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12912281875998107654652431 19368422813997161481978647)
      ·
        refine ⟨29052634220995742222967971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19368422813997161481978647 29052634220995742222967971)
        ·
          refine ⟨43578951331493613334451957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29052634220995742222967971 43578951331493613334451957)
          ·
            refine ⟨4085526687327526250104871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43578951331493613334451957 4085526687327526250104871)
            ·
              refine ⟨6128290030991289375157307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4085526687327526250104871 6128290030991289375157307)
              ·
                refine ⟨9192435046486934062735961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6128290030991289375157307 9192435046486934062735961)
                ·
                  refine ⟨6894326284865200547051971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9192435046486934062735961 6894326284865200547051971)
                  ·
                    refine ⟨10341489427297800820577957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6894326284865200547051971 10341489427297800820577957)
                    ·
                      refine ⟨1939029267618337653858367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10341489427297800820577957 1939029267618337653858367)
                      ·
                        rfl

theorem cell23_3776246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_3776246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776246 prefixEnd_3776246 := by exact prefixLift 3776246
  have htrace : WordTrace (prefixWord ++ tailWord_3776246) baseStart_3776246 baseEnd_3776246 := by
    simpa [prefixWord, tailWord_3776246, baseEnd_3776246] using wordTrace_append hprefix tailTrace_3776246
  have hstable : (prefixWord ++ tailWord_3776246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776246).length < 2 ^ (prefixWord ++ tailWord_3776246).sum := by decide
  have hdescent : baseEnd_3776246 < baseStart_3776246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776275 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 7]
def baseStart_3776275 : Nat := 118140960795 + 3776275 * 2 ^ 59
def prefixEnd_3776275 : Nat := 4983230072969 + 3 ^ 40 * 3776275 * 2
def baseEnd_3776275 : Nat := 1939044158557318040395733

theorem tailTrace_3776275 : CollatzResearch.WordTrace tailWord_3776275 prefixEnd_3776275 1939044158557318040395733 := by
  unfold tailWord_3776275
  simp only [CollatzResearch.WordTrace]
  refine ⟨137732064394208086269098279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91821376262805390846065519 137732064394208086269098279)
  ·
    refine ⟨206598096591312129403647419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137732064394208086269098279 206598096591312129403647419)
    ·
      refine ⟨309897144886968194105471129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206598096591312129403647419 309897144886968194105471129)
      ·
        refine ⟨232422858665226145579103347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309897144886968194105471129 232422858665226145579103347)
        ·
          refine ⟨348634287997839218368655021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232422858665226145579103347 348634287997839218368655021)
          ·
            refine ⟨130737857999189706888245633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 348634287997839218368655021 130737857999189706888245633)
            ·
              refine ⟨98053393499392280166184225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130737857999189706888245633 98053393499392280166184225)
              ·
                refine ⟨73540045124544210124638169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98053393499392280166184225 73540045124544210124638169)
                ·
                  refine ⟨55155033843408157593478627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73540045124544210124638169 55155033843408157593478627)
                  ·
                    refine ⟨82732550765112236390217941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55155033843408157593478627 82732550765112236390217941)
                    ·
                      refine ⟨1939044158557318040395733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 82732550765112236390217941 1939044158557318040395733)
                      ·
                        rfl

theorem cell23_3776275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 7].length) (baseStart_3776275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776275 prefixEnd_3776275 := by exact prefixLift 3776275
  have htrace : WordTrace (prefixWord ++ tailWord_3776275) baseStart_3776275 baseEnd_3776275 := by
    simpa [prefixWord, tailWord_3776275, baseEnd_3776275] using wordTrace_append hprefix tailTrace_3776275
  have hstable : (prefixWord ++ tailWord_3776275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776275).length < 2 ^ (prefixWord ++ tailWord_3776275).sum := by decide
  have hdescent : baseEnd_3776275 < baseStart_3776275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776289 : List Nat := [1, 2, 3, 2, 1, 3, 1, 2, 1, 5, 2]
def baseStart_3776289 : Nat := 118140960795 + 3776289 * 2 ^ 59
def prefixEnd_3776289 : Nat := 4983230072969 + 3 ^ 40 * 3776289 * 2
def baseEnd_3776289 : Nat := 1939051347286480985620669

theorem tailTrace_3776289 : CollatzResearch.WordTrace tailWord_3776289 prefixEnd_3776289 1939051347286480985620669 := by
  unfold tailWord_3776289
  simp only [CollatzResearch.WordTrace]
  refine ⟨137732575016157366660107921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91821716677438244440071947 137732575016157366660107921)
  ·
    refine ⟨103299431262118024995080941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137732575016157366660107921 103299431262118024995080941)
    ·
      refine ⟨38737286723294259373155353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103299431262118024995080941 38737286723294259373155353)
      ·
        refine ⟨29052965042470694529866515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38737286723294259373155353 29052965042470694529866515)
        ·
          refine ⟨43579447563706041794799773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29052965042470694529866515 43579447563706041794799773)
          ·
            refine ⟨16342292836389765673049915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43579447563706041794799773 16342292836389765673049915)
            ·
              refine ⟨24513439254584648509574873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16342292836389765673049915 24513439254584648509574873)
              ·
                refine ⟨18385079440938486382181155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24513439254584648509574873 18385079440938486382181155)
                ·
                  refine ⟨27577619161407729573271733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18385079440938486382181155 27577619161407729573271733)
                  ·
                    refine ⟨2585401796381974647494225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27577619161407729573271733 2585401796381974647494225)
                    ·
                      refine ⟨1939051347286480985620669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2585401796381974647494225 1939051347286480985620669)
                      ·
                        rfl

theorem cell23_3776289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_3776289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776289 prefixEnd_3776289 := by exact prefixLift 3776289
  have htrace : WordTrace (prefixWord ++ tailWord_3776289) baseStart_3776289 baseEnd_3776289 := by
    simpa [prefixWord, tailWord_3776289, baseEnd_3776289] using wordTrace_append hprefix tailTrace_3776289
  have hstable : (prefixWord ++ tailWord_3776289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776289).length < 2 ^ (prefixWord ++ tailWord_3776289).sum := by decide
  have hdescent : baseEnd_3776289 < baseStart_3776289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776296 : List Nat := [2, 1, 5, 1, 1, 2, 2, 2, 3, 1, 3]
def baseStart_3776296 : Nat := 118140960795 + 3776296 * 2 ^ 59
def prefixEnd_3776296 : Nat := 4983230072969 + 3 ^ 40 * 3776296 * 2
def baseEnd_3776296 : Nat := 1939054941651062458233137

theorem tailTrace_3776296 : CollatzResearch.WordTrace tailWord_3776296 prefixEnd_3776296 1939054941651062458233137 := by
  unfold tailWord_3776296
  simp only [CollatzResearch.WordTrace]
  refine ⟨68866415163566003427806371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91821886884754671237075161 68866415163566003427806371)
  ·
    refine ⟨103299622745349005141709557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68866415163566003427806371 103299622745349005141709557)
    ·
      refine ⟨9684339632376469232035271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103299622745349005141709557 9684339632376469232035271)
      ·
        refine ⟨14526509448564703848052907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9684339632376469232035271 14526509448564703848052907)
        ·
          refine ⟨21789764172847055772079361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14526509448564703848052907 21789764172847055772079361)
          ·
            refine ⟨16342323129635291829059521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21789764172847055772079361 16342323129635291829059521)
            ·
              refine ⟨12256742347226468871794641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16342323129635291829059521 12256742347226468871794641)
              ·
                refine ⟨9192556760419851653845981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12256742347226468871794641 9192556760419851653845981)
                ·
                  refine ⟨3447208785157444370192243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9192556760419851653845981 3447208785157444370192243)
                  ·
                    refine ⟨5170813177736166555288365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3447208785157444370192243 5170813177736166555288365)
                    ·
                      refine ⟨1939054941651062458233137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5170813177736166555288365 1939054941651062458233137)
                      ·
                        rfl

theorem cell23_3776296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_3776296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776296 prefixEnd_3776296 := by exact prefixLift 3776296
  have htrace : WordTrace (prefixWord ++ tailWord_3776296) baseStart_3776296 baseEnd_3776296 := by
    simpa [prefixWord, tailWord_3776296, baseEnd_3776296] using wordTrace_append hprefix tailTrace_3776296
  have hstable : (prefixWord ++ tailWord_3776296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776296).length < 2 ^ (prefixWord ++ tailWord_3776296).sum := by decide
  have hdescent : baseEnd_3776296 < baseStart_3776296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776329 : List Nat := [1, 2, 1, 1, 2, 4, 2, 4, 2, 4]
def baseStart_3776329 : Nat := 118140960795 + 3776329 * 2 ^ 59
def prefixEnd_3776329 : Nat := 4983230072969 + 3 ^ 40 * 3776329 * 2
def baseEnd_3776329 : Nat := 646357295504220276373495

theorem tailTrace_3776329 : CollatzResearch.WordTrace tailWord_3776329 prefixEnd_3776329 646357295504220276373495 := by
  unfold tailWord_3776329
  simp only [CollatzResearch.WordTrace]
  refine ⟨137734033936012453491564041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91822689290674968994376027 137734033936012453491564041)
  ·
    refine ⟨103300525452009340118673031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137734033936012453491564041 103300525452009340118673031)
    ·
      refine ⟨154950788178014010178009547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103300525452009340118673031 154950788178014010178009547)
      ·
        refine ⟨232426182267021015267014321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154950788178014010178009547 232426182267021015267014321)
        ·
          refine ⟨174319636700265761450260741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232426182267021015267014321 174319636700265761450260741)
          ·
            refine ⟨32684931881299830271923889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174319636700265761450260741 32684931881299830271923889)
            ·
              refine ⟨24513698910974872703942917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32684931881299830271923889 24513698910974872703942917)
              ·
                refine ⟨4596318545807788631989297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24513698910974872703942917 4596318545807788631989297)
                ·
                  refine ⟨3447238909355841473991973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4596318545807788631989297 3447238909355841473991973)
                  ·
                    refine ⟨646357295504220276373495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3447238909355841473991973 646357295504220276373495)
                    ·
                      rfl

theorem cell23_3776329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 2, 4].length) (baseStart_3776329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776329 prefixEnd_3776329 := by exact prefixLift 3776329
  have htrace : WordTrace (prefixWord ++ tailWord_3776329) baseStart_3776329 baseEnd_3776329 := by
    simpa [prefixWord, tailWord_3776329, baseEnd_3776329] using wordTrace_append hprefix tailTrace_3776329
  have hstable : (prefixWord ++ tailWord_3776329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776329).length < 2 ^ (prefixWord ++ tailWord_3776329).sum := by decide
  have hdescent : baseEnd_3776329 < baseStart_3776329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776356 : List Nat := [2, 3, 1, 1, 5, 1, 1, 1, 3, 2, 3]
def baseStart_3776356 : Nat := 118140960795 + 3776356 * 2 ^ 59
def prefixEnd_3776356 : Nat := 4983230072969 + 3 ^ 40 * 3776356 * 2
def baseEnd_3776356 : Nat := 1939085750490332223482861

theorem tailTrace_3776356 : CollatzResearch.WordTrace tailWord_3776356 prefixEnd_3776356 1939085750490332223482861 := by
  unfold tailWord_3776356
  simp only [CollatzResearch.WordTrace]
  refine ⟨68867509353457318551398461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91823345804609758068531281 68867509353457318551398461)
  ·
    refine ⟨25825316007546494456774423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68867509353457318551398461 25825316007546494456774423)
    ·
      refine ⟨38737974011319741685161635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25825316007546494456774423 38737974011319741685161635)
      ·
        refine ⟨58106961016979612527742453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38737974011319741685161635 58106961016979612527742453)
        ·
          refine ⟨5447527595341838674475855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58106961016979612527742453 5447527595341838674475855)
          ·
            refine ⟨8171291393012758011713783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5447527595341838674475855 8171291393012758011713783)
            ·
              refine ⟨12256937089519137017570675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8171291393012758011713783 12256937089519137017570675)
              ·
                refine ⟨18385405634278705526356013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12256937089519137017570675 18385405634278705526356013)
                ·
                  refine ⟨6894527112854514572383505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18385405634278705526356013 6894527112854514572383505)
                  ·
                    refine ⟨5170895334640885929287629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6894527112854514572383505 5170895334640885929287629)
                    ·
                      refine ⟨1939085750490332223482861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5170895334640885929287629 1939085750490332223482861)
                      ·
                        rfl

theorem cell23_3776356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_3776356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776356 prefixEnd_3776356 := by exact prefixLift 3776356
  have htrace : WordTrace (prefixWord ++ tailWord_3776356) baseStart_3776356 baseEnd_3776356 := by
    simpa [prefixWord, tailWord_3776356, baseEnd_3776356] using wordTrace_append hprefix tailTrace_3776356
  have hstable : (prefixWord ++ tailWord_3776356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776356).length < 2 ^ (prefixWord ++ tailWord_3776356).sum := by decide
  have hdescent : baseEnd_3776356 < baseStart_3776356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776366 : List Nat := [4, 1, 2, 3, 1, 2, 1, 2, 1, 2, 4]
def baseStart_3776366 : Nat := 118140960795 + 3776366 * 2 ^ 59
def prefixEnd_3776366 : Nat := 4983230072969 + 3 ^ 40 * 3776366 * 2
def baseEnd_3776366 : Nat := 1939090885296877184357815

theorem tailTrace_3776366 : CollatzResearch.WordTrace tailWord_3776366 prefixEnd_3776366 1939090885296877184357815 := by
  unfold tailWord_3776366
  simp only [CollatzResearch.WordTrace]
  refine ⟨17216922929609801101332619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91823588957918939207107301 17216922929609801101332619)
  ·
    refine ⟨25825384394414701651998929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17216922929609801101332619 25825384394414701651998929)
    ·
      refine ⟨19369038295811026238999197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25825384394414701651998929 19369038295811026238999197)
      ·
        refine ⟨7263389360929134839624699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19369038295811026238999197 7263389360929134839624699)
        ·
          refine ⟨10895084041393702259437049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7263389360929134839624699 10895084041393702259437049)
          ·
            refine ⟨8171313031045276694577787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10895084041393702259437049 8171313031045276694577787)
            ·
              refine ⟨12256969546567915041866681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8171313031045276694577787 12256969546567915041866681)
              ·
                refine ⟨9192727159925936281400011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12256969546567915041866681 9192727159925936281400011)
                ·
                  refine ⟨13789090739888904422100017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9192727159925936281400011 13789090739888904422100017)
                  ·
                    refine ⟨10341818054916678316575013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13789090739888904422100017 10341818054916678316575013)
                    ·
                      refine ⟨1939090885296877184357815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10341818054916678316575013 1939090885296877184357815)
                      ·
                        rfl

theorem cell23_3776366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_3776366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776366 prefixEnd_3776366 := by exact prefixLift 3776366
  have htrace : WordTrace (prefixWord ++ tailWord_3776366) baseStart_3776366 baseEnd_3776366 := by
    simpa [prefixWord, tailWord_3776366, baseEnd_3776366] using wordTrace_append hprefix tailTrace_3776366
  have hstable : (prefixWord ++ tailWord_3776366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776366).length < 2 ^ (prefixWord ++ tailWord_3776366).sum := by decide
  have hdescent : baseEnd_3776366 < baseStart_3776366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776369 : List Nat := [1, 2, 2, 2, 1, 3, 3, 2, 1, 3, 3]
def baseStart_3776369 : Nat := 118140960795 + 3776369 * 2 ^ 59
def prefixEnd_3776369 : Nat := 4983230072969 + 3 ^ 40 * 3776369 * 2
def baseEnd_3776369 : Nat := 1939092425738840672620301

theorem tailTrace_3776369 : CollatzResearch.WordTrace tailWord_3776369 prefixEnd_3776369 1939092425738840672620301 := by
  unfold tailWord_3776369
  simp only [CollatzResearch.WordTrace]
  refine ⟨137735492855867540323020161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91823661903911693548680107 137735492855867540323020161)
  ·
    refine ⟨103301619641900655242265121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137735492855867540323020161 103301619641900655242265121)
    ·
      refine ⟨77476214731425491431698841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103301619641900655242265121 77476214731425491431698841)
      ·
        refine ⟨58107161048569118573774131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77476214731425491431698841 58107161048569118573774131)
        ·
          refine ⟨87160741572853677860661197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58107161048569118573774131 87160741572853677860661197)
          ·
            refine ⟨32685278089820129197747949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87160741572853677860661197 32685278089820129197747949)
            ·
              refine ⟨12256979283682548449155481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32685278089820129197747949 12256979283682548449155481)
              ·
                refine ⟨9192734462761911336866611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12256979283682548449155481 9192734462761911336866611)
                ·
                  refine ⟨13789101694142867005299917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9192734462761911336866611 13789101694142867005299917)
                  ·
                    refine ⟨5170913135303575126987469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13789101694142867005299917 5170913135303575126987469)
                    ·
                      refine ⟨1939092425738840672620301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5170913135303575126987469 1939092425738840672620301)
                      ·
                        rfl

theorem cell23_3776369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_3776369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776369 prefixEnd_3776369 := by exact prefixLift 3776369
  have htrace : WordTrace (prefixWord ++ tailWord_3776369) baseStart_3776369 baseEnd_3776369 := by
    simpa [prefixWord, tailWord_3776369, baseEnd_3776369] using wordTrace_append hprefix tailTrace_3776369
  have hstable : (prefixWord ++ tailWord_3776369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776369).length < 2 ^ (prefixWord ++ tailWord_3776369).sum := by decide
  have hdescent : baseEnd_3776369 < baseStart_3776369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776373 : List Nat := [1, 3, 4, 1, 1, 1, 5, 1, 1, 2, 3]
def baseStart_3776373 : Nat := 118140960795 + 3776373 * 2 ^ 59
def prefixEnd_3776373 : Nat := 4983230072969 + 3 ^ 40 * 3776373 * 2
def baseEnd_3776373 : Nat := 1939094479661458656970283

theorem tailTrace_3776373 : CollatzResearch.WordTrace tailWord_3776373 prefixEnd_3776373 1939094479661458656970283 := by
  unfold tailWord_3776373
  simp only [CollatzResearch.WordTrace]
  refine ⟨137735638747853049006165773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91823759165235366004110515 137735638747853049006165773)
  ·
    refine ⟨51650864530444893377312165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137735638747853049006165773 51650864530444893377312165)
    ·
      refine ⟨9684537099458417508246031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51650864530444893377312165 9684537099458417508246031)
      ·
        refine ⟨14526805649187626262369047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9684537099458417508246031 14526805649187626262369047)
        ·
          refine ⟨21790208473781439393553571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14526805649187626262369047 21790208473781439393553571)
          ·
            refine ⟨32685312710672159090330357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21790208473781439393553571 32685312710672159090330357)
            ·
              refine ⟨3064248066625514914718471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32685312710672159090330357 3064248066625514914718471)
              ·
                refine ⟨4596372099938272372077707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3064248066625514914718471 4596372099938272372077707)
                ·
                  refine ⟨6894558149907408558116561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4596372099938272372077707 6894558149907408558116561)
                  ·
                    refine ⟨5170918612430556418587421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6894558149907408558116561 5170918612430556418587421)
                    ·
                      refine ⟨1939094479661458656970283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5170918612430556418587421 1939094479661458656970283)
                      ·
                        rfl

theorem cell23_3776373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_3776373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776373 prefixEnd_3776373 := by exact prefixLift 3776373
  have htrace : WordTrace (prefixWord ++ tailWord_3776373) baseStart_3776373 baseEnd_3776373 := by
    simpa [prefixWord, tailWord_3776373, baseEnd_3776373] using wordTrace_append hprefix tailTrace_3776373
  have hstable : (prefixWord ++ tailWord_3776373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776373).length < 2 ^ (prefixWord ++ tailWord_3776373).sum := by decide
  have hdescent : baseEnd_3776373 < baseStart_3776373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776387 : List Nat := [1, 1, 1, 3, 4, 4, 2, 2, 1, 2, 2]
def baseStart_3776387 : Nat := 118140960795 + 3776387 * 2 ^ 59
def prefixEnd_3776387 : Nat := 4983230072969 + 3 ^ 40 * 3776387 * 2
def baseEnd_3776387 : Nat := 1939101668390621602195219

theorem tailTrace_3776387 : CollatzResearch.WordTrace tailWord_3776387 prefixEnd_3776387 1939101668390621602195219 := by
  unfold tailWord_3776387
  simp only [CollatzResearch.WordTrace]
  refine ⟨137736149369802329397175415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91824099579868219598116943 137736149369802329397175415)
  ·
    refine ⟨206604224054703494095763123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137736149369802329397175415 206604224054703494095763123)
    ·
      refine ⟨309906336082055241143644685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206604224054703494095763123 309906336082055241143644685)
      ·
        refine ⟨116214876030770715428866757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309906336082055241143644685 116214876030770715428866757)
        ·
          refine ⟨21790289255769509142912517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116214876030770715428866757 21790289255769509142912517)
          ·
            refine ⟨4085679235456782964296097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21790289255769509142912517 4085679235456782964296097)
            ·
              refine ⟨3064259426592587223222073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4085679235456782964296097 3064259426592587223222073)
              ·
                refine ⟨2298194569944440417416555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3064259426592587223222073 2298194569944440417416555)
                ·
                  refine ⟨3447291854916660626124833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2298194569944440417416555 3447291854916660626124833)
                  ·
                    refine ⟨2585468891187495469593625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3447291854916660626124833 2585468891187495469593625)
                    ·
                      refine ⟨1939101668390621602195219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2585468891187495469593625 1939101668390621602195219)
                      ·
                        rfl

theorem cell23_3776387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 2, 1, 2, 2].length) (baseStart_3776387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776387 prefixEnd_3776387 := by exact prefixLift 3776387
  have htrace : WordTrace (prefixWord ++ tailWord_3776387) baseStart_3776387 baseEnd_3776387 := by
    simpa [prefixWord, tailWord_3776387, baseEnd_3776387] using wordTrace_append hprefix tailTrace_3776387
  have hstable : (prefixWord ++ tailWord_3776387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776387).length < 2 ^ (prefixWord ++ tailWord_3776387).sum := by decide
  have hdescent : baseEnd_3776387 < baseStart_3776387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776424 : List Nat := [2, 1, 6, 2, 2, 1, 2, 1, 1, 2, 3]
def baseStart_3776424 : Nat := 118140960795 + 3776424 * 2 ^ 59
def prefixEnd_3776424 : Nat := 4983230072969 + 3 ^ 40 * 3776424 * 2
def baseEnd_3776424 : Nat := 1939120667174837957432549

theorem tailTrace_3776424 : CollatzResearch.WordTrace tailWord_3776424 prefixEnd_3776424 1939120667174837957432549 := by
  unfold tailWord_3776424
  simp only [CollatzResearch.WordTrace]
  refine ⟨68868749435334142358136163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91824999247112189810848217 68868749435334142358136163)
  ·
    refine ⟨103303124153001213537204245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68868749435334142358136163 103303124153001213537204245)
    ·
      refine ⟨4842333944671931884556449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 103303124153001213537204245 4842333944671931884556449)
      ·
        refine ⟨3631750458503948913417337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4842333944671931884556449 3631750458503948913417337)
        ·
          refine ⟨2723812843877961685063003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3631750458503948913417337 2723812843877961685063003)
          ·
            refine ⟨4085719265816942527594505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2723812843877961685063003 4085719265816942527594505)
            ·
              refine ⟨3064289449362706895695879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4085719265816942527594505 3064289449362706895695879)
              ·
                refine ⟨4596434174044060343543819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3064289449362706895695879 4596434174044060343543819)
                ·
                  refine ⟨6894651261066090515315729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4596434174044060343543819 6894651261066090515315729)
                  ·
                    refine ⟨5170988445799567886486797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6894651261066090515315729 5170988445799567886486797)
                    ·
                      refine ⟨1939120667174837957432549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5170988445799567886486797 1939120667174837957432549)
                      ·
                        rfl

theorem cell23_3776424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_3776424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776424 prefixEnd_3776424 := by exact prefixLift 3776424
  have htrace : WordTrace (prefixWord ++ tailWord_3776424) baseStart_3776424 baseEnd_3776424 := by
    simpa [prefixWord, tailWord_3776424, baseEnd_3776424] using wordTrace_append hprefix tailTrace_3776424
  have hstable : (prefixWord ++ tailWord_3776424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776424).length < 2 ^ (prefixWord ++ tailWord_3776424).sum := by decide
  have hdescent : baseEnd_3776424 < baseStart_3776424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776442 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 1, 1, 9]
def baseStart_3776442 : Nat := 118140960795 + 3776442 * 2 ^ 59
def prefixEnd_3776442 : Nat := 4983230072969 + 3 ^ 40 * 3776442 * 2
def baseEnd_3776442 : Nat := 1939129909826618887007465

theorem tailTrace_3776442 : CollatzResearch.WordTrace tailWord_3776442 prefixEnd_3776442 1939129909826618887007465 := by
  unfold tailWord_3776442
  simp only [CollatzResearch.WordTrace]
  refine ⟨34434538846150768447606895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91825436923068715860285053 34434538846150768447606895)
  ·
    refine ⟨51651808269226152671410343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34434538846150768447606895 51651808269226152671410343)
    ·
      refine ⟨77477712403839229007115515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51651808269226152671410343 77477712403839229007115515)
      ·
        refine ⟨116216568605758843510673273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77477712403839229007115515 116216568605758843510673273)
        ·
          refine ⟨87162426454319132633004955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116216568605758843510673273 87162426454319132633004955)
          ·
            refine ⟨130743639681478698949507433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87162426454319132633004955 130743639681478698949507433)
            ·
              refine ⟨98057729761109024212130575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130743639681478698949507433 98057729761109024212130575)
              ·
                refine ⟨147086594641663536318195863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98057729761109024212130575 147086594641663536318195863)
                ·
                  refine ⟨220629891962495304477293795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147086594641663536318195863 220629891962495304477293795)
                  ·
                    refine ⟨330944837943742956715940693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 220629891962495304477293795 330944837943742956715940693)
                    ·
                      refine ⟨1939129909826618887007465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 330944837943742956715940693 1939129909826618887007465)
                      ·
                        rfl

theorem cell23_3776442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_3776442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776442 prefixEnd_3776442 := by exact prefixLift 3776442
  have htrace : WordTrace (prefixWord ++ tailWord_3776442) baseStart_3776442 baseEnd_3776442 := by
    simpa [prefixWord, tailWord_3776442, baseEnd_3776442] using wordTrace_append hprefix tailTrace_3776442
  have hstable : (prefixWord ++ tailWord_3776442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776442).length < 2 ^ (prefixWord ++ tailWord_3776442).sum := by decide
  have hdescent : baseEnd_3776442 < baseStart_3776442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776459 : List Nat := [1, 1, 1, 1, 3, 4, 1, 3, 2, 3, 3]
def baseStart_3776459 : Nat := 118140960795 + 3776459 * 2 ^ 59
def prefixEnd_3776459 : Nat := 4983230072969 + 3 ^ 40 * 3776459 * 2
def baseEnd_3776459 : Nat := 1939138638997745320494887

theorem tailTrace_3776459 : CollatzResearch.WordTrace tailWord_3776459 prefixEnd_3776459 1939138638997745320494887 := by
  unfold tailWord_3776459
  simp only [CollatzResearch.WordTrace]
  refine ⟨137738775425541485693796431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91825850283694323795864287 137738775425541485693796431)
  ·
    refine ⟨206608163138312228540694647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137738775425541485693796431 206608163138312228540694647)
    ·
      refine ⟨309912244707468342811041971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206608163138312228540694647 309912244707468342811041971)
      ·
        refine ⟨464868367061202514216562957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309912244707468342811041971 464868367061202514216562957)
        ·
          refine ⟨174325637647950942831211109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 464868367061202514216562957 174325637647950942831211109)
          ·
            refine ⟨32686057058990801780852083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174325637647950942831211109 32686057058990801780852083)
            ·
              refine ⟨49029085588486202671278125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32686057058990801780852083 49029085588486202671278125)
              ·
                refine ⟨18385907095682326001729297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49029085588486202671278125 18385907095682326001729297)
                ·
                  refine ⟨13789430321761744501296973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18385907095682326001729297 13789430321761744501296973)
                  ·
                    refine ⟨5171036370660654187986365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13789430321761744501296973 5171036370660654187986365)
                    ·
                      refine ⟨1939138638997745320494887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5171036370660654187986365 1939138638997745320494887)
                      ·
                        rfl

theorem cell23_3776459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 3, 3].length) (baseStart_3776459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776459 prefixEnd_3776459 := by exact prefixLift 3776459
  have htrace : WordTrace (prefixWord ++ tailWord_3776459) baseStart_3776459 baseEnd_3776459 := by
    simpa [prefixWord, tailWord_3776459, baseEnd_3776459] using wordTrace_append hprefix tailTrace_3776459
  have hstable : (prefixWord ++ tailWord_3776459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776459).length < 2 ^ (prefixWord ++ tailWord_3776459).sum := by decide
  have hdescent : baseEnd_3776459 < baseStart_3776459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776479 : List Nat := [1, 1, 2, 3, 4, 1, 2, 1, 1, 7]
def baseStart_3776479 : Nat := 118140960795 + 3776479 * 2 ^ 59
def prefixEnd_3776479 : Nat := 4983230072969 + 3 ^ 40 * 3776479 * 2
def baseEnd_3776479 : Nat := 646382969536945080748265

theorem tailTrace_3776479 : CollatzResearch.WordTrace tailWord_3776479 prefixEnd_3776479 646382969536945080748265 := by
  unfold tailWord_3776479
  simp only [CollatzResearch.WordTrace]
  refine ⟨137739504885469029109524491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91826336590312686073016327 137739504885469029109524491)
  ·
    refine ⟨206609257328203543664286737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137739504885469029109524491 206609257328203543664286737)
    ·
      refine ⟨154956942996152657748215053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206609257328203543664286737 154956942996152657748215053)
      ·
        refine ⟨58108853623557246655580645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154956942996152657748215053 58108853623557246655580645)
        ·
          refine ⟨10895410054416983747921371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58108853623557246655580645 10895410054416983747921371)
          ·
            refine ⟨16343115081625475621882057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10895410054416983747921371 16343115081625475621882057)
            ·
              refine ⟨12257336311219106716411543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16343115081625475621882057 12257336311219106716411543)
              ·
                refine ⟨18386004466828660074617315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12257336311219106716411543 18386004466828660074617315)
                ·
                  refine ⟨27579006700242990111925973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18386004466828660074617315 27579006700242990111925973)
                  ·
                    refine ⟨646382969536945080748265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27579006700242990111925973 646382969536945080748265)
                    ·
                      rfl

theorem cell23_3776479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 7].length) (baseStart_3776479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776479 prefixEnd_3776479 := by exact prefixLift 3776479
  have htrace : WordTrace (prefixWord ++ tailWord_3776479) baseStart_3776479 baseEnd_3776479 := by
    simpa [prefixWord, tailWord_3776479, baseEnd_3776479] using wordTrace_append hprefix tailTrace_3776479
  have hstable : (prefixWord ++ tailWord_3776479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776479).length < 2 ^ (prefixWord ++ tailWord_3776479).sum := by decide
  have hdescent : baseEnd_3776479 < baseStart_3776479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776483 : List Nat := [1, 1, 1, 6, 1, 4, 1, 3, 5]
def baseStart_3776483 : Nat := 118140960795 + 3776483 * 2 ^ 59
def prefixEnd_3776483 : Nat := 4983230072969 + 3 ^ 40 * 3776483 * 2
def baseEnd_3776483 : Nat := 215461218059272580732753

theorem tailTrace_3776483 : CollatzResearch.WordTrace tailWord_3776483 prefixEnd_3776483 215461218059272580732753 := by
  unfold tailWord_3776483
  simp only [CollatzResearch.WordTrace]
  refine ⟨137739650777454537792670103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91826433851636358528446735 137739650777454537792670103)
  ·
    refine ⟨206609476166181806689005155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137739650777454537792670103 206609476166181806689005155)
    ·
      refine ⟨309914214249272710033507733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206609476166181806689005155 309914214249272710033507733)
      ·
        refine ⟨14527228792934658282820675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 309914214249272710033507733 14527228792934658282820675)
        ·
          refine ⟨21790843189401987424231013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14527228792934658282820675 21790843189401987424231013)
          ·
            refine ⟨4085783098012872642043315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21790843189401987424231013 4085783098012872642043315)
            ·
              refine ⟨6128674647019308963064973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4085783098012872642043315 6128674647019308963064973)
              ·
                refine ⟨2298252992632240861149365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6128674647019308963064973 2298252992632240861149365)
                ·
                  refine ⟨215461218059272580732753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2298252992632240861149365 215461218059272580732753)
                  ·
                    rfl

theorem cell23_3776483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 3, 5].length) (baseStart_3776483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776483 prefixEnd_3776483 := by exact prefixLift 3776483
  have htrace : WordTrace (prefixWord ++ tailWord_3776483) baseStart_3776483 baseEnd_3776483 := by
    simpa [prefixWord, tailWord_3776483, baseEnd_3776483] using wordTrace_append hprefix tailTrace_3776483
  have hstable : (prefixWord ++ tailWord_3776483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776483).length < 2 ^ (prefixWord ++ tailWord_3776483).sum := by decide
  have hdescent : baseEnd_3776483 < baseStart_3776483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776526 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 5, 4]
def baseStart_3776526 : Nat := 118140960795 + 3776526 * 2 ^ 59
def prefixEnd_3776526 : Nat := 4983230072969 + 3 ^ 40 * 3776526 * 2
def baseEnd_3776526 : Nat := 646391014067198852785693

theorem tailTrace_3776526 : CollatzResearch.WordTrace tailWord_3776526 prefixEnd_3776526 646391014067198852785693 := by
  unfold tailWord_3776526
  simp only [CollatzResearch.WordTrace]
  refine ⟨17217652389537344517060679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91827479410865837424323621 17217652389537344517060679)
  ·
    refine ⟨25826478584306016775591019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17217652389537344517060679 25826478584306016775591019)
    ·
      refine ⟨38739717876459025163386529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25826478584306016775591019 38739717876459025163386529)
      ·
        refine ⟨29054788407344268872539897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38739717876459025163386529 29054788407344268872539897)
        ·
          refine ⟨21791091305508201654404923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29054788407344268872539897 21791091305508201654404923)
          ·
            refine ⟨32686636958262302481607385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21791091305508201654404923 32686636958262302481607385)
            ·
              refine ⟨24514977718696726861205539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32686636958262302481607385 24514977718696726861205539)
              ·
                refine ⟨36772466578045090291808309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24514977718696726861205539 36772466578045090291808309)
                ·
                  refine ⟨3447418741691727214857029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36772466578045090291808309 3447418741691727214857029)
                  ·
                    refine ⟨646391014067198852785693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3447418741691727214857029 646391014067198852785693)
                    ·
                      rfl

theorem cell23_3776526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_3776526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776526 prefixEnd_3776526 := by exact prefixLift 3776526
  have htrace : WordTrace (prefixWord ++ tailWord_3776526) baseStart_3776526 baseEnd_3776526 := by
    simpa [prefixWord, tailWord_3776526, baseEnd_3776526] using wordTrace_append hprefix tailTrace_3776526
  have hstable : (prefixWord ++ tailWord_3776526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776526).length < 2 ^ (prefixWord ++ tailWord_3776526).sum := by decide
  have hdescent : baseEnd_3776526 < baseStart_3776526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776533 : List Nat := [1, 3, 2, 1, 5, 1, 2, 1, 2, 1, 4]
def baseStart_3776533 : Nat := 118140960795 + 3776533 * 2 ^ 59
def prefixEnd_3776533 : Nat := 4983230072969 + 3 ^ 40 * 3776533 * 2
def baseEnd_3776533 : Nat := 1939176636566178030969547

theorem tailTrace_3776533 : CollatzResearch.WordTrace tailWord_3776533 prefixEnd_3776533 1939176636566178030969547 := by
  unfold tailWord_3776533
  simp only [CollatzResearch.WordTrace]
  refine ⟨137741474427273396331990253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91827649618182264221326835 137741474427273396331990253)
  ·
    refine ⟨51653052910227523624496345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137741474427273396331990253 51653052910227523624496345)
    ·
      refine ⟨38739789682670642718372259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51653052910227523624496345 38739789682670642718372259)
      ·
        refine ⟨58109684524005964077558389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38739789682670642718372259 58109684524005964077558389)
        ·
          refine ⟨5447782924125559132271099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58109684524005964077558389 5447782924125559132271099)
          ·
            refine ⟨8171674386188338698406649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5447782924125559132271099 8171674386188338698406649)
            ·
              refine ⟨6128755789641254023804987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8171674386188338698406649 6128755789641254023804987)
              ·
                refine ⟨9193133684461881035707481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6128755789641254023804987 9193133684461881035707481)
                ·
                  refine ⟨6894850263346410776780611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9193133684461881035707481 6894850263346410776780611)
                  ·
                    refine ⟨10342275395019616165170917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6894850263346410776780611 10342275395019616165170917)
                    ·
                      refine ⟨1939176636566178030969547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10342275395019616165170917 1939176636566178030969547)
                      ·
                        rfl

theorem cell23_3776533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_3776533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776533 prefixEnd_3776533 := by exact prefixLift 3776533
  have htrace : WordTrace (prefixWord ++ tailWord_3776533) baseStart_3776533 baseEnd_3776533 := by
    simpa [prefixWord, tailWord_3776533, baseEnd_3776533] using wordTrace_append hprefix tailTrace_3776533
  have hstable : (prefixWord ++ tailWord_3776533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776533).length < 2 ^ (prefixWord ++ tailWord_3776533).sum := by decide
  have hdescent : baseEnd_3776533 < baseStart_3776533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776543 : List Nat := [1, 1, 2, 4, 1, 2, 2, 5, 1, 4]
def baseStart_3776543 : Nat := 118140960795 + 3776543 * 2 ^ 59
def prefixEnd_3776543 : Nat := 4983230072969 + 3 ^ 40 * 3776543 * 2
def baseEnd_3776543 : Nat := 646393923790907663948167

theorem tailTrace_3776543 : CollatzResearch.WordTrace tailWord_3776543 prefixEnd_3776543 646393923790907663948167 := by
  unfold tailWord_3776543
  simp only [CollatzResearch.WordTrace]
  refine ⟨137741839157237168039854283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91827892771491445359902855 137741839157237168039854283)
  ·
    refine ⟨206612758735855752059781425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137741839157237168039854283 206612758735855752059781425)
    ·
      refine ⟨154959569051891814044836069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206612758735855752059781425 154959569051891814044836069)
      ·
        refine ⟨29054919197229715133406763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154959569051891814044836069 29054919197229715133406763)
        ·
          refine ⟨43582378795844572700110145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29054919197229715133406763 43582378795844572700110145)
          ·
            refine ⟨32686784096883429525082609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43582378795844572700110145 32686784096883429525082609)
            ·
              refine ⟨24515088072662572143811957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32686784096883429525082609 24515088072662572143811957)
              ·
                refine ⟨2298289506812116138482371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24515088072662572143811957 2298289506812116138482371)
                ·
                  refine ⟨3447434260218174207723557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2298289506812116138482371 3447434260218174207723557)
                  ·
                    refine ⟨646393923790907663948167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3447434260218174207723557 646393923790907663948167)
                    ·
                      rfl

theorem cell23_3776543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 5, 1, 4].length) (baseStart_3776543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776543 prefixEnd_3776543 := by exact prefixLift 3776543
  have htrace : WordTrace (prefixWord ++ tailWord_3776543) baseStart_3776543 baseEnd_3776543 := by
    simpa [prefixWord, tailWord_3776543, baseEnd_3776543] using wordTrace_append hprefix tailTrace_3776543
  have hstable : (prefixWord ++ tailWord_3776543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776543).length < 2 ^ (prefixWord ++ tailWord_3776543).sum := by decide
  have hdescent : baseEnd_3776543 < baseStart_3776543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776560 : List Nat := [2, 1, 1, 1, 2, 5, 4, 2, 1, 4]
def baseStart_3776560 : Nat := 118140960795 + 3776560 * 2 ^ 59
def prefixEnd_3776560 : Nat := 4983230072969 + 3 ^ 40 * 3776560 * 2
def baseEnd_3776560 : Nat := 646396833514616475110641

theorem tailTrace_3776560 : CollatzResearch.WordTrace tailWord_3776560 prefixEnd_3776560 646396833514616475110641 := by
  unfold tailWord_3776560
  simp only [CollatzResearch.WordTrace]
  refine ⟨68871229599087789971611567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91828306132117053295482089 68871229599087789971611567)
  ·
    refine ⟨103306844398631684957417351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68871229599087789971611567 103306844398631684957417351)
    ·
      refine ⟨154960266597947527436126027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103306844398631684957417351 154960266597947527436126027)
      ·
        refine ⟨232440399896921291154189041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154960266597947527436126027 232440399896921291154189041)
        ·
          refine ⟨174330299922690968365641781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232440399896921291154189041 174330299922690968365641781)
          ·
            refine ⟨16343465617752278284278917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 174330299922690968365641781 16343465617752278284278917)
            ·
              refine ⟨3064399803328552178302297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16343465617752278284278917 3064399803328552178302297)
              ·
                refine ⟨2298299852496414133726723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3064399803328552178302297 2298299852496414133726723)
                ·
                  refine ⟨3447449778744621200590085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2298299852496414133726723 3447449778744621200590085)
                  ·
                    refine ⟨646396833514616475110641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3447449778744621200590085 646396833514616475110641)
                    ·
                      rfl

theorem cell23_3776560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 2, 1, 4].length) (baseStart_3776560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776560 prefixEnd_3776560 := by exact prefixLift 3776560
  have htrace : WordTrace (prefixWord ++ tailWord_3776560) baseStart_3776560 baseEnd_3776560 := by
    simpa [prefixWord, tailWord_3776560, baseEnd_3776560] using wordTrace_append hprefix tailTrace_3776560
  have hstable : (prefixWord ++ tailWord_3776560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776560).length < 2 ^ (prefixWord ++ tailWord_3776560).sum := by decide
  have hdescent : baseEnd_3776560 < baseStart_3776560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776583 : List Nat := [1, 1, 4, 1, 3, 1, 3, 2, 3, 1, 3]
def baseStart_3776583 : Nat := 118140960795 + 3776583 * 2 ^ 59
def prefixEnd_3776583 : Nat := 4983230072969 + 3 ^ 40 * 3776583 * 2
def baseEnd_3776583 : Nat := 1939202310598902835344317

theorem tailTrace_3776583 : CollatzResearch.WordTrace tailWord_3776583 prefixEnd_3776583 1939202310598902835344317 := by
  unfold tailWord_3776583
  simp only [CollatzResearch.WordTrace]
  refine ⟨137743298077092254871310403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91828865384728169914206935 137743298077092254871310403)
  ·
    refine ⟨206614947115638382306965605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137743298077092254871310403 206614947115638382306965605)
    ·
      refine ⟨38740302584182196682556051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206614947115638382306965605 38740302584182196682556051)
      ·
        refine ⟨58110453876273295023834077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38740302584182196682556051 58110453876273295023834077)
        ·
          refine ⟨21791420203602485633937779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58110453876273295023834077 21791420203602485633937779)
          ·
            refine ⟨32687130305403728450906669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21791420203602485633937779 32687130305403728450906669)
            ·
              refine ⟨12257673864526398169090001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32687130305403728450906669 12257673864526398169090001)
              ·
                refine ⟨9193255398394798626817501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12257673864526398169090001 9193255398394798626817501)
                ·
                  refine ⟨3447470774398049485056563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9193255398394798626817501 3447470774398049485056563)
                  ·
                    refine ⟨5171206161597074227584845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3447470774398049485056563 5171206161597074227584845)
                    ·
                      refine ⟨1939202310598902835344317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5171206161597074227584845 1939202310598902835344317)
                      ·
                        rfl

theorem cell23_3776583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 3, 1, 3].length) (baseStart_3776583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776583 prefixEnd_3776583 := by exact prefixLift 3776583
  have htrace : WordTrace (prefixWord ++ tailWord_3776583) baseStart_3776583 baseEnd_3776583 := by
    simpa [prefixWord, tailWord_3776583, baseEnd_3776583] using wordTrace_append hprefix tailTrace_3776583
  have hstable : (prefixWord ++ tailWord_3776583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776583).length < 2 ^ (prefixWord ++ tailWord_3776583).sum := by decide
  have hdescent : baseEnd_3776583 < baseStart_3776583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776586 : List Nat := [3, 1, 2, 1, 1, 2, 1, 6, 1, 5]
def baseStart_3776586 : Nat := 118140960795 + 3776586 * 2 ^ 59
def prefixEnd_3776586 : Nat := 4983230072969 + 3 ^ 40 * 3776586 * 2
def baseEnd_3776586 : Nat := 646401283680288774535601

theorem tailTrace_3776586 : CollatzResearch.WordTrace tailWord_3776586 prefixEnd_3776586 646401283680288774535601 := by
  unfold tailWord_3776586
  simp only [CollatzResearch.WordTrace]
  refine ⟨34435851874020346595917403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91828938330720924255779741 34435851874020346595917403)
  ·
    refine ⟨51653777811030519893876105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34435851874020346595917403 51653777811030519893876105)
    ·
      refine ⟨38740333358272889920407079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51653777811030519893876105 38740333358272889920407079)
      ·
        refine ⟨58110500037409334880610619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38740333358272889920407079 58110500037409334880610619)
        ·
          refine ⟨87165750056114002320915929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58110500037409334880610619 87165750056114002320915929)
          ·
            refine ⟨65374312542085501740686947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87165750056114002320915929 65374312542085501740686947)
            ·
              refine ⟨98061468813128252611030421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65374312542085501740686947 98061468813128252611030421)
              ·
                refine ⟨4596631350615386841142051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98061468813128252611030421 4596631350615386841142051)
                ·
                  refine ⟨6894947025923080261713077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4596631350615386841142051 6894947025923080261713077)
                  ·
                    refine ⟨646401283680288774535601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6894947025923080261713077 646401283680288774535601)
                    ·
                      rfl

theorem cell23_3776586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_3776586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776586 prefixEnd_3776586 := by exact prefixLift 3776586
  have htrace : WordTrace (prefixWord ++ tailWord_3776586) baseStart_3776586 baseEnd_3776586 := by
    simpa [prefixWord, tailWord_3776586, baseEnd_3776586] using wordTrace_append hprefix tailTrace_3776586
  have hstable : (prefixWord ++ tailWord_3776586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776586).length < 2 ^ (prefixWord ++ tailWord_3776586).sum := by decide
  have hdescent : baseEnd_3776586 < baseStart_3776586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776600 : List Nat := [2, 1, 2, 2, 1, 4, 1, 5, 1, 1, 3]
def baseStart_3776600 : Nat := 118140960795 + 3776600 * 2 ^ 59
def prefixEnd_3776600 : Nat := 4983230072969 + 3 ^ 40 * 3776600 * 2
def baseEnd_3776600 : Nat := 1939211039770029268831739

theorem tailTrace_3776600 : CollatzResearch.WordTrace tailWord_3776600 prefixEnd_3776600 1939211039770029268831739 := by
  unfold tailWord_3776600
  simp only [CollatzResearch.WordTrace]
  refine ⟨68871959059015333387339627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91829278745353777849786169 68871959059015333387339627)
  ·
    refine ⟨103307938588523000081009441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68871959059015333387339627 103307938588523000081009441)
    ·
      refine ⟨77480953941392250060757081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103307938588523000081009441 77480953941392250060757081)
      ·
        refine ⟨58110715456044187545567811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77480953941392250060757081 58110715456044187545567811)
        ·
          refine ⟨87166073184066281318351717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58110715456044187545567811 87166073184066281318351717)
          ·
            refine ⟨16343638722012427747190947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87166073184066281318351717 16343638722012427747190947)
            ·
              refine ⟨24515458083018641620786421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16343638722012427747190947 24515458083018641620786421)
              ·
                refine ⟨2298324195282997651948727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24515458083018641620786421 2298324195282997651948727)
                ·
                  refine ⟨3447486292924496477923091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2298324195282997651948727 3447486292924496477923091)
                  ·
                    refine ⟨5171229439386744716884637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3447486292924496477923091 5171229439386744716884637)
                    ·
                      refine ⟨1939211039770029268831739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5171229439386744716884637 1939211039770029268831739)
                      ·
                        rfl

theorem cell23_3776600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 5, 1, 1, 3].length) (baseStart_3776600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776600 prefixEnd_3776600 := by exact prefixLift 3776600
  have htrace : WordTrace (prefixWord ++ tailWord_3776600) baseStart_3776600 baseEnd_3776600 := by
    simpa [prefixWord, tailWord_3776600, baseEnd_3776600] using wordTrace_append hprefix tailTrace_3776600
  have hstable : (prefixWord ++ tailWord_3776600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776600).length < 2 ^ (prefixWord ++ tailWord_3776600).sum := by decide
  have hdescent : baseEnd_3776600 < baseStart_3776600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776619 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 4]
def baseStart_3776619 : Nat := 118140960795 + 3776619 * 2 ^ 59
def prefixEnd_3776619 : Nat := 4983230072969 + 3 ^ 40 * 3776619 * 2
def baseEnd_3776619 : Nat := 1939220795902464694494151

theorem tailTrace_3776619 : CollatzResearch.WordTrace tailWord_3776619 prefixEnd_3776619 1939220795902464694494151 := by
  unfold tailWord_3776619
  simp only [CollatzResearch.WordTrace]
  refine ⟨137744611104961833019620911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91829740736641222013080607 137744611104961833019620911)
  ·
    refine ⟨206616916657442749529431367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137744611104961833019620911 206616916657442749529431367)
    ·
      refine ⟨309925374986164124294147051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206616916657442749529431367 309925374986164124294147051)
      ·
        refine ⟨464888062479246186441220577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309925374986164124294147051 464888062479246186441220577)
        ·
          refine ⟨348666046859434639830915433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464888062479246186441220577 348666046859434639830915433)
          ·
            refine ⟨261499535144575979873186575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348666046859434639830915433 261499535144575979873186575)
            ·
              refine ⟨392249302716863969809779863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261499535144575979873186575 392249302716863969809779863)
              ·
                refine ⟨588373954075295954714669795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 392249302716863969809779863 588373954075295954714669795)
                ·
                  refine ⟨882560931112943932072004693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 588373954075295954714669795 882560931112943932072004693)
                  ·
                    refine ⟨10342510911479811703968805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 882560931112943932072004693 10342510911479811703968805)
                    ·
                      refine ⟨1939220795902464694494151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10342510911479811703968805 1939220795902464694494151)
                      ·
                        rfl

theorem cell23_3776619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 4].length) (baseStart_3776619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776619 prefixEnd_3776619 := by exact prefixLift 3776619
  have htrace : WordTrace (prefixWord ++ tailWord_3776619) baseStart_3776619 baseEnd_3776619 := by
    simpa [prefixWord, tailWord_3776619, baseEnd_3776619] using wordTrace_append hprefix tailTrace_3776619
  have hstable : (prefixWord ++ tailWord_3776619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776619).length < 2 ^ (prefixWord ++ tailWord_3776619).sum := by decide
  have hdescent : baseEnd_3776619 < baseStart_3776619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776626 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 3, 1, 5]
def baseStart_3776626 : Nat := 118140960795 + 3776626 * 2 ^ 59
def prefixEnd_3776626 : Nat := 4983230072969 + 3 ^ 40 * 3776626 * 2
def baseEnd_3776626 : Nat := 1939224390267046167106619

theorem tailTrace_3776626 : CollatzResearch.WordTrace tailWord_3776626 prefixEnd_3776626 1939224390267046167106619 := by
  unfold tailWord_3776626
  simp only [CollatzResearch.WordTrace]
  refine ⟨34436216603984118303781433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91829910943957648810083821 34436216603984118303781433)
  ·
    refine ⟨25827162452988088727836075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34436216603984118303781433 25827162452988088727836075)
    ·
      refine ⟨38740743679482133091754113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25827162452988088727836075 38740743679482133091754113)
      ·
        refine ⟨29055557759611599818815585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38740743679482133091754113 29055557759611599818815585)
        ·
          refine ⟨21791668319708699864111689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29055557759611599818815585 21791668319708699864111689)
          ·
            refine ⟨16343751239781524898083767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21791668319708699864111689 16343751239781524898083767)
            ·
              refine ⟨24515626859672287347125651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16343751239781524898083767 24515626859672287347125651)
              ·
                refine ⟨36773440289508431020688477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24515626859672287347125651 36773440289508431020688477)
                ·
                  refine ⟨13790040108565661632758179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36773440289508431020688477 13790040108565661632758179)
                  ·
                    refine ⟨20685060162848492449137269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13790040108565661632758179 20685060162848492449137269)
                    ·
                      refine ⟨1939224390267046167106619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20685060162848492449137269 1939224390267046167106619)
                      ·
                        rfl

theorem cell23_3776626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_3776626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776626 prefixEnd_3776626 := by exact prefixLift 3776626
  have htrace : WordTrace (prefixWord ++ tailWord_3776626) baseStart_3776626 baseEnd_3776626 := by
    simpa [prefixWord, tailWord_3776626, baseEnd_3776626] using wordTrace_append hprefix tailTrace_3776626
  have hstable : (prefixWord ++ tailWord_3776626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776626).length < 2 ^ (prefixWord ++ tailWord_3776626).sum := by decide
  have hdescent : baseEnd_3776626 < baseStart_3776626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776633 : List Nat := [1, 2, 1, 3, 4, 3, 1, 1, 1, 6]
def baseStart_3776633 : Nat := 118140960795 + 3776633 * 2 ^ 59
def prefixEnd_3776633 : Nat := 4983230072969 + 3 ^ 40 * 3776633 * 2
def baseEnd_3776633 : Nat := 646409328210542546573029

theorem tailTrace_3776633 : CollatzResearch.WordTrace tailWord_3776633 prefixEnd_3776633 646409328210542546573029 := by
  unfold tailWord_3776633
  simp only [CollatzResearch.WordTrace]
  refine ⟨137745121726911113410630553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91830081151274075607087035 137745121726911113410630553)
  ·
    refine ⟨103308841295183335057972915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137745121726911113410630553 103308841295183335057972915)
    ·
      refine ⟨154963261942775002586959373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103308841295183335057972915 154963261942775002586959373)
      ·
        refine ⟨58111223228540625970109765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154963261942775002586959373 58111223228540625970109765)
        ·
          refine ⟨10895854355351367369395581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58111223228540625970109765 10895854355351367369395581)
          ·
            refine ⟨4085945383256762763523343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10895854355351367369395581 4085945383256762763523343)
            ·
              refine ⟨6128918074885144145285015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4085945383256762763523343 6128918074885144145285015)
              ·
                refine ⟨9193377112327716217927523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6128918074885144145285015 9193377112327716217927523)
                ·
                  refine ⟨13790065668491574326891285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9193377112327716217927523 13790065668491574326891285)
                  ·
                    refine ⟨646409328210542546573029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13790065668491574326891285 646409328210542546573029)
                    ·
                      rfl

theorem cell23_3776633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 6].length) (baseStart_3776633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776633 prefixEnd_3776633 := by exact prefixLift 3776633
  have htrace : WordTrace (prefixWord ++ tailWord_3776633) baseStart_3776633 baseEnd_3776633 := by
    simpa [prefixWord, tailWord_3776633, baseEnd_3776633] using wordTrace_append hprefix tailTrace_3776633
  have hstable : (prefixWord ++ tailWord_3776633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776633).length < 2 ^ (prefixWord ++ tailWord_3776633).sum := by decide
  have hdescent : baseEnd_3776633 < baseStart_3776633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776636 : List Nat := [2, 2, 2, 1, 1, 5, 1, 1, 1, 1, 6]
def baseStart_3776636 : Nat := 118140960795 + 3776636 * 2 ^ 59
def prefixEnd_3776636 : Nat := 4983230072969 + 3 ^ 40 * 3776636 * 2
def baseEnd_3776636 : Nat := 1939229525073591127981573

theorem tailTrace_3776636 : CollatzResearch.WordTrace tailWord_3776636 prefixEnd_3776636 1939229525073591127981573 := by
  unfold tailWord_3776636
  simp only [CollatzResearch.WordTrace]
  refine ⟨68872615572950122461494881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91830154097266829948659841 68872615572950122461494881)
  ·
    refine ⟨51654461679712591846121161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68872615572950122461494881 51654461679712591846121161)
    ·
      refine ⟨38740846259784443884590871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51654461679712591846121161 38740846259784443884590871)
      ·
        refine ⟨58111269389676665826886307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38740846259784443884590871 58111269389676665826886307)
        ·
          refine ⟨87166904084514998740329461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58111269389676665826886307 87166904084514998740329461)
          ·
            refine ⟨8171897257923281131905887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87166904084514998740329461 8171897257923281131905887)
            ·
              refine ⟨12257845886884921697858831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8171897257923281131905887 12257845886884921697858831)
              ·
                refine ⟨18386768830327382546788247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12257845886884921697858831 18386768830327382546788247)
                ·
                  refine ⟨27580153245491073820182371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18386768830327382546788247 27580153245491073820182371)
                  ·
                    refine ⟨41370229868236610730273557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27580153245491073820182371 41370229868236610730273557)
                    ·
                      refine ⟨1939229525073591127981573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41370229868236610730273557 1939229525073591127981573)
                      ·
                        rfl

theorem cell23_3776636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_3776636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776636 prefixEnd_3776636 := by exact prefixLift 3776636
  have htrace : WordTrace (prefixWord ++ tailWord_3776636) baseStart_3776636 baseEnd_3776636 := by
    simpa [prefixWord, tailWord_3776636, baseEnd_3776636] using wordTrace_append hprefix tailTrace_3776636
  have hstable : (prefixWord ++ tailWord_3776636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776636).length < 2 ^ (prefixWord ++ tailWord_3776636).sum := by decide
  have hdescent : baseEnd_3776636 < baseStart_3776636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776643 : List Nat := [1, 1, 1, 3, 3, 3, 1, 4, 1, 2, 3]
def baseStart_3776643 : Nat := 118140960795 + 3776643 * 2 ^ 59
def prefixEnd_3776643 : Nat := 4983230072969 + 3 ^ 40 * 3776643 * 2
def baseEnd_3776643 : Nat := 1939233119438172600594041

theorem tailTrace_3776643 : CollatzResearch.WordTrace tailWord_3776643 prefixEnd_3776643 1939233119438172600594041 := by
  unfold tailWord_3776643
  simp only [CollatzResearch.WordTrace]
  refine ⟨137745486456874885118494583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91830324304583256745663055 137745486456874885118494583)
  ·
    refine ⟨206618229685312327677741875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137745486456874885118494583 206618229685312327677741875)
    ·
      refine ⟨309927344527968491516612813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206618229685312327677741875 309927344527968491516612813)
      ·
        refine ⟨116222754197988184318729805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309927344527968491516612813 116222754197988184318729805)
        ·
          refine ⟨43583532824245569119523677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116222754197988184318729805 43583532824245569119523677)
          ·
            refine ⟨16343824809092088419821379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43583532824245569119523677 16343824809092088419821379)
            ·
              refine ⟨24515737213638132629732069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16343824809092088419821379 24515737213638132629732069)
              ·
                refine ⟨4596700727557149868074763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24515737213638132629732069 4596700727557149868074763)
                ·
                  refine ⟨6895051091335724802112145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4596700727557149868074763 6895051091335724802112145)
                  ·
                    refine ⟨5171288318501793601584109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6895051091335724802112145 5171288318501793601584109)
                    ·
                      refine ⟨1939233119438172600594041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5171288318501793601584109 1939233119438172600594041)
                      ·
                        rfl

theorem cell23_3776643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 2, 3].length) (baseStart_3776643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776643 prefixEnd_3776643 := by exact prefixLift 3776643
  have htrace : WordTrace (prefixWord ++ tailWord_3776643) baseStart_3776643 baseEnd_3776643 := by
    simpa [prefixWord, tailWord_3776643, baseEnd_3776643] using wordTrace_append hprefix tailTrace_3776643
  have hstable : (prefixWord ++ tailWord_3776643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776643).length < 2 ^ (prefixWord ++ tailWord_3776643).sum := by decide
  have hdescent : baseEnd_3776643 < baseStart_3776643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776656 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 3]
def baseStart_3776656 : Nat := 118140960795 + 3776656 * 2 ^ 59
def prefixEnd_3776656 : Nat := 4983230072969 + 3 ^ 40 * 3776656 * 2
def baseEnd_3776656 : Nat := 1939239794686681049731481

theorem tailTrace_3776656 : CollatzResearch.WordTrace tailWord_3776656 prefixEnd_3776656 1939239794686681049731481 := by
  unfold tailWord_3776656
  simp only [CollatzResearch.WordTrace]
  refine ⟨68872980302913894169358911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91830640403885192225811881 68872980302913894169358911)
  ·
    refine ⟨103309470454370841254038367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68872980302913894169358911 103309470454370841254038367)
    ·
      refine ⟨154964205681556261881057551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103309470454370841254038367 154964205681556261881057551)
      ·
        refine ⟨232446308522334392821586327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154964205681556261881057551 232446308522334392821586327)
        ·
          refine ⟨348669462783501589232379491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232446308522334392821586327 348669462783501589232379491)
          ·
            refine ⟨523004194175252383848569237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348669462783501589232379491 523004194175252383848569237)
            ·
              refine ⟨24515821601964955492901683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 523004194175252383848569237 24515821601964955492901683)
              ·
                refine ⟨36773732402947433239352525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24515821601964955492901683 36773732402947433239352525)
                ·
                  refine ⟨13790149651105287464757197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36773732402947433239352525 13790149651105287464757197)
                  ·
                    refine ⟨5171306119164482799283949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13790149651105287464757197 5171306119164482799283949)
                    ·
                      refine ⟨1939239794686681049731481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5171306119164482799283949 1939239794686681049731481)
                      ·
                        rfl

theorem cell23_3776656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 3].length) (baseStart_3776656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776656 prefixEnd_3776656 := by exact prefixLift 3776656
  have htrace : WordTrace (prefixWord ++ tailWord_3776656) baseStart_3776656 baseEnd_3776656 := by
    simpa [prefixWord, tailWord_3776656, baseEnd_3776656] using wordTrace_append hprefix tailTrace_3776656
  have hstable : (prefixWord ++ tailWord_3776656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776656).length < 2 ^ (prefixWord ++ tailWord_3776656).sum := by decide
  have hdescent : baseEnd_3776656 < baseStart_3776656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776659 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 1, 9]
def baseStart_3776659 : Nat := 118140960795 + 3776659 * 2 ^ 59
def prefixEnd_3776659 : Nat := 4983230072969 + 3 ^ 40 * 3776659 * 2
def baseEnd_3776659 : Nat := 646413778376214845997989

theorem tailTrace_3776659 : CollatzResearch.WordTrace tailWord_3776659 prefixEnd_3776659 646413778376214845997989 := by
  unfold tailWord_3776659
  simp only [CollatzResearch.WordTrace]
  refine ⟨137746070024816919851077031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91830713349877946567384687 137746070024816919851077031)
  ·
    refine ⟨206619105037225379776615547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137746070024816919851077031 206619105037225379776615547)
    ·
      refine ⟨309928657555838069664923321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206619105037225379776615547 309928657555838069664923321)
      ·
        refine ⟨232446493166878552248692491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309928657555838069664923321 232446493166878552248692491)
        ·
          refine ⟨348669739750317828373038737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232446493166878552248692491 348669739750317828373038737)
          ·
            refine ⟨261502304812738371279779053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348669739750317828373038737 261502304812738371279779053)
            ·
              refine ⟨98063364304776889229917145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261502304812738371279779053 98063364304776889229917145)
              ·
                refine ⟨73547523228582666922437859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98063364304776889229917145 73547523228582666922437859)
                ·
                  refine ⟨110321284842874000383656789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73547523228582666922437859 110321284842874000383656789)
                  ·
                    refine ⟨646413778376214845997989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 110321284842874000383656789 646413778376214845997989)
                    ·
                      rfl

theorem cell23_3776659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 9].length) (baseStart_3776659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776659 prefixEnd_3776659 := by exact prefixLift 3776659
  have htrace : WordTrace (prefixWord ++ tailWord_3776659) baseStart_3776659 baseEnd_3776659 := by
    simpa [prefixWord, tailWord_3776659, baseEnd_3776659] using wordTrace_append hprefix tailTrace_3776659
  have hstable : (prefixWord ++ tailWord_3776659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776659).length < 2 ^ (prefixWord ++ tailWord_3776659).sum := by decide
  have hdescent : baseEnd_3776659 < baseStart_3776659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776663 : List Nat := [1, 1, 3, 3, 5, 1, 9]
def baseStart_3776663 : Nat := 118140960795 + 3776663 * 2 ^ 59
def prefixEnd_3776663 : Nat := 4983230072969 + 3 ^ 40 * 3776663 * 2
def baseEnd_3776663 : Nat := 23941276408040278053629

theorem tailTrace_3776663 : CollatzResearch.WordTrace tailWord_3776663 prefixEnd_3776663 23941276408040278053629 := by
  unfold tailWord_3776663
  simp only [CollatzResearch.WordTrace]
  refine ⟨137746215916802428534222643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91830810611201619022815095 137746215916802428534222643)
  ·
    refine ⟨206619323875203642801333965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137746215916802428534222643 206619323875203642801333965)
    ·
      refine ⟨77482246453201366050500237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206619323875203642801333965 77482246453201366050500237)
      ·
        refine ⟨29055842419950512268937589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77482246453201366050500237 29055842419950512268937589)
        ·
          refine ⟨2723985226870360525212899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29055842419950512268937589 2723985226870360525212899)
          ·
            refine ⟨4085977840305540787819349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2723985226870360525212899 4085977840305540787819349)
            ·
              refine ⟨23941276408040278053629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4085977840305540787819349 23941276408040278053629)
              ·
                rfl

theorem cell23_3776663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 9].length) (baseStart_3776663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776663 prefixEnd_3776663 := by exact prefixLift 3776663
  have htrace : WordTrace (prefixWord ++ tailWord_3776663) baseStart_3776663 baseEnd_3776663 := by
    simpa [prefixWord, tailWord_3776663, baseEnd_3776663] using wordTrace_append hprefix tailTrace_3776663
  have hstable : (prefixWord ++ tailWord_3776663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776663).length < 2 ^ (prefixWord ++ tailWord_3776663).sum := by decide
  have hdescent : baseEnd_3776663 < baseStart_3776663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776674 : List Nat := [3, 3, 1, 3, 1, 3, 1, 1, 3, 2, 2]
def baseStart_3776674 : Nat := 118140960795 + 3776674 * 2 ^ 59
def prefixEnd_3776674 : Nat := 4983230072969 + 3 ^ 40 * 3776674 * 2
def baseEnd_3776674 : Nat := 1939249037338461979306399

theorem tailTrace_3776674 : CollatzResearch.WordTrace tailWord_3776674 prefixEnd_3776674 1939249037338461979306399 := by
  unfold tailWord_3776674
  simp only [CollatzResearch.WordTrace]
  refine ⟨34436654279940644353218269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91831078079841718275248717 34436654279940644353218269)
  ·
    refine ⟨12913745354977741632456851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34436654279940644353218269 12913745354977741632456851)
    ·
      refine ⟨19370618032466612448685277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12913745354977741632456851 19370618032466612448685277)
      ·
        refine ⟨7263981762174979668256979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19370618032466612448685277 7263981762174979668256979)
        ·
          refine ⟨10895972643262469502385469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7263981762174979668256979 10895972643262469502385469)
          ·
            refine ⟨4085989741223426063394551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10895972643262469502385469 4085989741223426063394551)
            ·
              refine ⟨6128984611835139095091827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4085989741223426063394551 6128984611835139095091827)
              ·
                refine ⟨9193476917752708642637741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6128984611835139095091827 9193476917752708642637741)
                ·
                  refine ⟨3447553844157265740989153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9193476917752708642637741 3447553844157265740989153)
                  ·
                    refine ⟨2585665383117949305741865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3447553844157265740989153 2585665383117949305741865)
                    ·
                      refine ⟨1939249037338461979306399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2585665383117949305741865 1939249037338461979306399)
                      ·
                        rfl

theorem cell23_3776674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_3776674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776674 prefixEnd_3776674 := by exact prefixLift 3776674
  have htrace : WordTrace (prefixWord ++ tailWord_3776674) baseStart_3776674 baseEnd_3776674 := by
    simpa [prefixWord, tailWord_3776674, baseEnd_3776674] using wordTrace_append hprefix tailTrace_3776674
  have hstable : (prefixWord ++ tailWord_3776674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776674).length < 2 ^ (prefixWord ++ tailWord_3776674).sum := by decide
  have hdescent : baseEnd_3776674 < baseStart_3776674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776690 : List Nat := [3, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3]
def baseStart_3776690 : Nat := 118140960795 + 3776690 * 2 ^ 59
def prefixEnd_3776690 : Nat := 4983230072969 + 3 ^ 40 * 3776690 * 2
def baseEnd_3776690 : Nat := 1939257253028933916706325

theorem tailTrace_3776690 : CollatzResearch.WordTrace tailWord_3776690 prefixEnd_3776690 1939257253028933916706325 := by
  unfold tailWord_3776690
  simp only [CollatzResearch.WordTrace]
  refine ⟨34436800171926153036363881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91831467125136408096970349 34436800171926153036363881)
  ·
    refine ⟨25827600128944614777272911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34436800171926153036363881 25827600128944614777272911)
    ·
      refine ⟨38741400193416922165909367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25827600128944614777272911 38741400193416922165909367)
      ·
        refine ⟨58112100290125383248864051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38741400193416922165909367 58112100290125383248864051)
        ·
          refine ⟨87168150435188074873296077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58112100290125383248864051 87168150435188074873296077)
          ·
            refine ⟨32688056413195528077486029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87168150435188074873296077 32688056413195528077486029)
            ·
              refine ⟨12258021154948323029057261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32688056413195528077486029 12258021154948323029057261)
              ·
                refine ⟨4596757933105621135896473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12258021154948323029057261 4596757933105621135896473)
                ·
                  refine ⟨3447568449829215851922355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4596757933105621135896473 3447568449829215851922355)
                  ·
                    refine ⟨5171352674743823777883533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3447568449829215851922355 5171352674743823777883533)
                    ·
                      refine ⟨1939257253028933916706325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5171352674743823777883533 1939257253028933916706325)
                      ·
                        rfl

theorem cell23_3776690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3].length) (baseStart_3776690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776690 prefixEnd_3776690 := by exact prefixLift 3776690
  have htrace : WordTrace (prefixWord ++ tailWord_3776690) baseStart_3776690 baseEnd_3776690 := by
    simpa [prefixWord, tailWord_3776690, baseEnd_3776690] using wordTrace_append hprefix tailTrace_3776690
  have hstable : (prefixWord ++ tailWord_3776690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776690).length < 2 ^ (prefixWord ++ tailWord_3776690).sum := by decide
  have hdescent : baseEnd_3776690 < baseStart_3776690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776730 : List Nat := [3, 1, 1, 2, 2, 1, 2, 3, 4, 2, 2]
def baseStart_3776730 : Nat := 118140960795 + 3776730 * 2 ^ 59
def prefixEnd_3776730 : Nat := 4983230072969 + 3 ^ 40 * 3776730 * 2
def baseEnd_3776730 : Nat := 1939277792255113760206141

theorem tailTrace_3776730 : CollatzResearch.WordTrace tailWord_3776730 prefixEnd_3776730 1939277792255113760206141 := by
  unfold tailWord_3776730
  simp only [CollatzResearch.WordTrace]
  refine ⟨34437164901889924744227911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91832439738373132651274429 34437164901889924744227911)
  ·
    refine ⟨51655747352834887116341867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34437164901889924744227911 51655747352834887116341867)
    ·
      refine ⟨77483621029252330674512801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51655747352834887116341867 77483621029252330674512801)
      ·
        refine ⟨58112715771939248005884601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77483621029252330674512801 58112715771939248005884601)
        ·
          refine ⟨43584536828954436004413451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58112715771939248005884601 43584536828954436004413451)
          ·
            refine ⟨65376805243431654006620177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43584536828954436004413451 65376805243431654006620177)
            ·
              refine ⟨49032603932573740504965133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65376805243431654006620177 49032603932573740504965133)
              ·
                refine ⟨18387226474715152689361925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49032603932573740504965133 18387226474715152689361925)
                ·
                  refine ⟨3447604964009091129255361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18387226474715152689361925 3447604964009091129255361)
                  ·
                    refine ⟨2585703723006818346941521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3447604964009091129255361 2585703723006818346941521)
                    ·
                      refine ⟨1939277792255113760206141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2585703723006818346941521 1939277792255113760206141)
                      ·
                        rfl

theorem cell23_3776730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 4, 2, 2].length) (baseStart_3776730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776730 prefixEnd_3776730 := by exact prefixLift 3776730
  have htrace : WordTrace (prefixWord ++ tailWord_3776730) baseStart_3776730 baseEnd_3776730 := by
    simpa [prefixWord, tailWord_3776730, baseEnd_3776730] using wordTrace_append hprefix tailTrace_3776730
  have hstable : (prefixWord ++ tailWord_3776730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776730).length < 2 ^ (prefixWord ++ tailWord_3776730).sum := by decide
  have hdescent : baseEnd_3776730 < baseStart_3776730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776736 : List Nat := [2, 1, 1, 3, 1, 3, 2, 3, 7]
def baseStart_3776736 : Nat := 118140960795 + 3776736 * 2 ^ 59
def prefixEnd_3776736 : Nat := 4983230072969 + 3 ^ 40 * 3776736 * 2
def baseEnd_3776736 : Nat := 215475652571004526303457

theorem tailTrace_3776736 : CollatzResearch.WordTrace tailWord_3776736 prefixEnd_3776736 215475652571004526303457 := by
  unfold tailWord_3776736
  simp only [CollatzResearch.WordTrace]
  refine ⟨68874439222768981000815031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91832585630358641334420041 68874439222768981000815031)
  ·
    refine ⟨103311658834153471501222547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68874439222768981000815031 103311658834153471501222547)
    ·
      refine ⟨154967488251230207251833821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103311658834153471501222547 154967488251230207251833821)
      ·
        refine ⟨58112808094211327719437683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154967488251230207251833821 58112808094211327719437683)
        ·
          refine ⟨87169212141316991579156525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58112808094211327719437683 87169212141316991579156525)
          ·
            refine ⟨32688454552993871842183697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87169212141316991579156525 32688454552993871842183697)
            ·
              refine ⟨24516340914745403881637773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32688454552993871842183697 24516340914745403881637773)
              ·
                refine ⟨9193627843029526455614165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24516340914745403881637773 9193627843029526455614165)
                ·
                  refine ⟨215475652571004526303457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9193627843029526455614165 215475652571004526303457)
                  ·
                    rfl

theorem cell23_3776736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 7].length) (baseStart_3776736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776736 prefixEnd_3776736 := by exact prefixLift 3776736
  have htrace : WordTrace (prefixWord ++ tailWord_3776736) baseStart_3776736 baseEnd_3776736 := by
    simpa [prefixWord, tailWord_3776736, baseEnd_3776736] using wordTrace_append hprefix tailTrace_3776736
  have hstable : (prefixWord ++ tailWord_3776736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776736).length < 2 ^ (prefixWord ++ tailWord_3776736).sum := by decide
  have hdescent : baseEnd_3776736 < baseStart_3776736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776743 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 4]
def baseStart_3776743 : Nat := 118140960795 + 3776743 * 2 ^ 59
def prefixEnd_3776743 : Nat := 4983230072969 + 3 ^ 40 * 3776743 * 2
def baseEnd_3776743 : Nat := 1939284467503622209343581

theorem tailTrace_3776743 : CollatzResearch.WordTrace tailWord_3776743 prefixEnd_3776743 1939284467503622209343581 := by
  unfold tailWord_3776743
  simp only [CollatzResearch.WordTrace]
  refine ⟨137749133756512602197134883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91832755837675068131423255 137749133756512602197134883)
  ·
    refine ⟨206623700634768903295702325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137749133756512602197134883 206623700634768903295702325)
    ·
      refine ⟨19370971934509584683972093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 206623700634768903295702325 19370971934509584683972093)
      ·
        refine ⟨7264114475441094256489535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19370971934509584683972093 7264114475441094256489535)
        ·
          refine ⟨10896171713161641384734303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7264114475441094256489535 10896171713161641384734303)
          ·
            refine ⟨16344257569742462077101455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10896171713161641384734303 16344257569742462077101455)
            ·
              refine ⟨24516386354613693115652183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16344257569742462077101455 24516386354613693115652183)
              ·
                refine ⟨36774579531920539673478275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24516386354613693115652183 36774579531920539673478275)
                ·
                  refine ⟨55161869297880809510217413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36774579531920539673478275 55161869297880809510217413)
                  ·
                    refine ⟨10342850493352651783165765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55161869297880809510217413 10342850493352651783165765)
                    ·
                      refine ⟨1939284467503622209343581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10342850493352651783165765 1939284467503622209343581)
                      ·
                        rfl

theorem cell23_3776743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_3776743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776743 prefixEnd_3776743 := by exact prefixLift 3776743
  have htrace : WordTrace (prefixWord ++ tailWord_3776743) baseStart_3776743 baseEnd_3776743 := by
    simpa [prefixWord, tailWord_3776743, baseEnd_3776743] using wordTrace_append hprefix tailTrace_3776743
  have hstable : (prefixWord ++ tailWord_3776743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776743).length < 2 ^ (prefixWord ++ tailWord_3776743).sum := by decide
  have hdescent : baseEnd_3776743 < baseStart_3776743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776773 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 1, 7, 2]
def baseStart_3776773 : Nat := 118140960795 + 3776773 * 2 ^ 59
def prefixEnd_3776773 : Nat := 4983230072969 + 3 ^ 40 * 3776773 * 2
def baseEnd_3776773 : Nat := 1939299871923257091968443

theorem tailTrace_3776773 : CollatzResearch.WordTrace tailWord_3776773 prefixEnd_3776773 1939299871923257091968443 := by
  unfold tailWord_3776773
  simp only [CollatzResearch.WordTrace]
  refine ⟨137750227946403917320726973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91833485297602611547151315 137750227946403917320726973)
  ·
    refine ⟨51656335479901468995272615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137750227946403917320726973 51656335479901468995272615)
    ·
      refine ⟨77484503219852203492908923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51656335479901468995272615 77484503219852203492908923)
      ·
        refine ⟨116226754829778305239363385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77484503219852203492908923 116226754829778305239363385)
        ·
          refine ⟨87170066122333728929522539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116226754829778305239363385 87170066122333728929522539)
          ·
            refine ⟨130755099183500593394283809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87170066122333728929522539 130755099183500593394283809)
            ·
              refine ⟨98066324387625445045712857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130755099183500593394283809 98066324387625445045712857)
              ·
                refine ⟨73549743290719083784284643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98066324387625445045712857 73549743290719083784284643)
                ·
                  refine ⟨110324614936078625676426965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73549743290719083784284643 110324614936078625676426965)
                  ·
                    refine ⟨2585733162564342789291257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 110324614936078625676426965 2585733162564342789291257)
                    ·
                      refine ⟨1939299871923257091968443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2585733162564342789291257 1939299871923257091968443)
                      ·
                        rfl

theorem cell23_3776773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 7, 2].length) (baseStart_3776773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776773 prefixEnd_3776773 := by exact prefixLift 3776773
  have htrace : WordTrace (prefixWord ++ tailWord_3776773) baseStart_3776773 baseEnd_3776773 := by
    simpa [prefixWord, tailWord_3776773, baseEnd_3776773] using wordTrace_append hprefix tailTrace_3776773
  have hstable : (prefixWord ++ tailWord_3776773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776773).length < 2 ^ (prefixWord ++ tailWord_3776773).sum := by decide
  have hdescent : baseEnd_3776773 < baseStart_3776773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776798 : List Nat := [4, 3, 2, 1, 1, 2, 3, 1, 2, 2, 2]
def baseStart_3776798 : Nat := 118140960795 + 3776798 * 2 ^ 59
def prefixEnd_3776798 : Nat := 4983230072969 + 3 ^ 40 * 3776798 * 2
def baseEnd_3776798 : Nat := 1939312708939619494155829

theorem tailTrace_3776798 : CollatzResearch.WordTrace tailWord_3776798 prefixEnd_3776798 1939312708939619494155829 := by
  unfold tailWord_3776798
  simp only [CollatzResearch.WordTrace]
  refine ⟨17218892471414168323798381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91834093180875564393591365 17218892471414168323798381)
  ·
    refine ⟨6457084676780313121424393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17218892471414168323798381 6457084676780313121424393)
    ·
      refine ⟨4842813507585234841068295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6457084676780313121424393 4842813507585234841068295)
      ·
        refine ⟨7264220261377852261602443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4842813507585234841068295 7264220261377852261602443)
        ·
          refine ⟨10896330392066778392403665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7264220261377852261602443 10896330392066778392403665)
          ·
            refine ⟨8172247794050083794302749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10896330392066778392403665 8172247794050083794302749)
            ·
              refine ⟨3064592922768781422863531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8172247794050083794302749 3064592922768781422863531)
              ·
                refine ⟨4596889384153172134295297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3064592922768781422863531 4596889384153172134295297)
                ·
                  refine ⟨3447667038114879100721473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4596889384153172134295297 3447667038114879100721473)
                  ·
                    refine ⟨2585750278586159325541105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3447667038114879100721473 2585750278586159325541105)
                    ·
                      refine ⟨1939312708939619494155829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2585750278586159325541105 1939312708939619494155829)
                      ·
                        rfl

theorem cell23_3776798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_3776798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776798 prefixEnd_3776798 := by exact prefixLift 3776798
  have htrace : WordTrace (prefixWord ++ tailWord_3776798) baseStart_3776798 baseEnd_3776798 := by
    simpa [prefixWord, tailWord_3776798, baseEnd_3776798] using wordTrace_append hprefix tailTrace_3776798
  have hstable : (prefixWord ++ tailWord_3776798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776798).length < 2 ^ (prefixWord ++ tailWord_3776798).sum := by decide
  have hdescent : baseEnd_3776798 < baseStart_3776798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776816 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 6]
def baseStart_3776816 : Nat := 118140960795 + 3776816 * 2 ^ 59
def prefixEnd_3776816 : Nat := 4983230072969 + 3 ^ 40 * 3776816 * 2
def baseEnd_3776816 : Nat := 1939321951591400423730745

theorem tailTrace_3776816 : CollatzResearch.WordTrace tailWord_3776816 prefixEnd_3776816 1939321951591400423730745 := by
  unfold tailWord_3776816
  simp only [CollatzResearch.WordTrace]
  refine ⟨68875898142624067832271151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91834530856832090443028201 68875898142624067832271151)
  ·
    refine ⟨103313847213936101748406727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68875898142624067832271151 103313847213936101748406727)
    ·
      refine ⟨154970770820904152622610091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103313847213936101748406727 154970770820904152622610091)
      ·
        refine ⟨232456156231356228933915137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154970770820904152622610091 232456156231356228933915137)
        ·
          refine ⟨174342117173517171700436353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232456156231356228933915137 174342117173517171700436353)
          ·
            refine ⟨130756587880137878775327265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174342117173517171700436353 130756587880137878775327265)
            ·
              refine ⟨98067440910103409081495449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130756587880137878775327265 98067440910103409081495449)
              ·
                refine ⟨73550580682577556811121587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98067440910103409081495449 73550580682577556811121587)
                ·
                  refine ⟨110325871023866335216682381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73550580682577556811121587 110325871023866335216682381)
                  ·
                    refine ⟨41372201633949875706255893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110325871023866335216682381 41372201633949875706255893)
                    ·
                      refine ⟨1939321951591400423730745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41372201633949875706255893 1939321951591400423730745)
                      ·
                        rfl

theorem cell23_3776816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 6].length) (baseStart_3776816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776816 prefixEnd_3776816 := by exact prefixLift 3776816
  have htrace : WordTrace (prefixWord ++ tailWord_3776816) baseStart_3776816 baseEnd_3776816 := by
    simpa [prefixWord, tailWord_3776816, baseEnd_3776816] using wordTrace_append hprefix tailTrace_3776816
  have hstable : (prefixWord ++ tailWord_3776816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776816).length < 2 ^ (prefixWord ++ tailWord_3776816).sum := by decide
  have hdescent : baseEnd_3776816 < baseStart_3776816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776820 : List Nat := [2, 5, 1, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_3776820 : Nat := 118140960795 + 3776820 * 2 ^ 59
def prefixEnd_3776820 : Nat := 4983230072969 + 3 ^ 40 * 3776820 * 2
def baseEnd_3776820 : Nat := 1939324005514018408080727

theorem tailTrace_3776820 : CollatzResearch.WordTrace tailWord_3776820 prefixEnd_3776820 1939324005514018408080727 := by
  unfold tailWord_3776820
  simp only [CollatzResearch.WordTrace]
  refine ⟨68875971088616822173843957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91834628118155762898458609 68875971088616822173843957)
  ·
    refine ⟨6457122289557827078797871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68875971088616822173843957 6457122289557827078797871)
    ·
      refine ⟨9685683434336740618196807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6457122289557827078797871 9685683434336740618196807)
      ·
        refine ⟨14528525151505110927295211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9685683434336740618196807 14528525151505110927295211)
        ·
          refine ⟨21792787727257666390942817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14528525151505110927295211 21792787727257666390942817)
          ·
            refine ⟨16344590795443249793207113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21792787727257666390942817 16344590795443249793207113)
            ·
              refine ⟨12258443096582437344905335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16344590795443249793207113 12258443096582437344905335)
              ·
                refine ⟨18387664644873656017358003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12258443096582437344905335 18387664644873656017358003)
                ·
                  refine ⟨27581496967310484026037005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18387664644873656017358003 27581496967310484026037005)
                  ·
                    refine ⟨10343061362741431509763877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27581496967310484026037005 10343061362741431509763877)
                    ·
                      refine ⟨1939324005514018408080727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10343061362741431509763877 1939324005514018408080727)
                      ·
                        rfl

theorem cell23_3776820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_3776820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776820 prefixEnd_3776820 := by exact prefixLift 3776820
  have htrace : WordTrace (prefixWord ++ tailWord_3776820) baseStart_3776820 baseEnd_3776820 := by
    simpa [prefixWord, tailWord_3776820, baseEnd_3776820] using wordTrace_append hprefix tailTrace_3776820
  have hstable : (prefixWord ++ tailWord_3776820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776820).length < 2 ^ (prefixWord ++ tailWord_3776820).sum := by decide
  have hdescent : baseEnd_3776820 < baseStart_3776820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776823 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 6, 2, 3]
def baseStart_3776823 : Nat := 118140960795 + 3776823 * 2 ^ 59
def prefixEnd_3776823 : Nat := 4983230072969 + 3 ^ 40 * 3776823 * 2
def baseEnd_3776823 : Nat := 1939325545955981896343213

theorem tailTrace_3776823 : CollatzResearch.WordTrace tailWord_3776823 prefixEnd_3776823 1939325545955981896343213 := by
  unfold tailWord_3776823
  simp only [CollatzResearch.WordTrace]
  refine ⟨137752051596222775860047123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91834701064148517240031415 137752051596222775860047123)
  ·
    refine ⟨206628077394334163790070685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137752051596222775860047123 206628077394334163790070685)
    ·
      refine ⟨77485529022875311421276507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206628077394334163790070685 77485529022875311421276507)
      ·
        refine ⟨116228293534312967131914761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77485529022875311421276507 116228293534312967131914761)
        ·
          refine ⟨87171220150734725348936071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116228293534312967131914761 87171220150734725348936071)
          ·
            refine ⟨130756830226102088023404107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87171220150734725348936071 130756830226102088023404107)
            ·
              refine ⟨196135245339153132035106161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130756830226102088023404107 196135245339153132035106161)
              ·
                refine ⟨147101434004364849026329621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196135245339153132035106161 147101434004364849026329621)
                ·
                  refine ⟨6895379718954602298109201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 147101434004364849026329621 6895379718954602298109201)
                  ·
                    refine ⟨5171534789215951723581901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6895379718954602298109201 5171534789215951723581901)
                    ·
                      refine ⟨1939325545955981896343213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5171534789215951723581901 1939325545955981896343213)
                      ·
                        rfl

theorem cell23_3776823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 2, 3].length) (baseStart_3776823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776823 prefixEnd_3776823 := by exact prefixLift 3776823
  have htrace : WordTrace (prefixWord ++ tailWord_3776823) baseStart_3776823 baseEnd_3776823 := by
    simpa [prefixWord, tailWord_3776823, baseEnd_3776823] using wordTrace_append hprefix tailTrace_3776823
  have hstable : (prefixWord ++ tailWord_3776823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776823).length < 2 ^ (prefixWord ++ tailWord_3776823).sum := by decide
  have hdescent : baseEnd_3776823 < baseStart_3776823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776873 : List Nat := [1, 2, 1, 1, 1, 3, 5, 1, 3, 5]
def baseStart_3776873 : Nat := 118140960795 + 3776873 * 2 ^ 59
def prefixEnd_3776873 : Nat := 4983230072969 + 3 ^ 40 * 3776873 * 2
def baseEnd_3776873 : Nat := 646450406662902233572661

theorem tailTrace_3776873 : CollatzResearch.WordTrace tailWord_3776873 prefixEnd_3776873 646450406662902233572661 := by
  unfold tailWord_3776873
  simp only [CollatzResearch.WordTrace]
  refine ⟨137753875246041634399367273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91835916830694422932911515 137753875246041634399367273)
  ·
    refine ⟨103315406434531225799525455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137753875246041634399367273 103315406434531225799525455)
    ·
      refine ⟨154973109651796838699288183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103315406434531225799525455 154973109651796838699288183)
      ·
        refine ⟨232459664477695258048932275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154973109651796838699288183 232459664477695258048932275)
        ·
          refine ⟨348689496716542887073398413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232459664477695258048932275 348689496716542887073398413)
          ·
            refine ⟨130758561268703582652524405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 348689496716542887073398413 130758561268703582652524405)
            ·
              refine ⟨12258615118940960873674163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130758561268703582652524405 12258615118940960873674163)
              ·
                refine ⟨18387922678411441310511245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12258615118940960873674163 18387922678411441310511245)
                ·
                  refine ⟨6895471004404290491441717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18387922678411441310511245 6895471004404290491441717)
                  ·
                    refine ⟨646450406662902233572661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6895471004404290491441717 646450406662902233572661)
                    ·
                      rfl

theorem cell23_3776873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 5].length) (baseStart_3776873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776873 prefixEnd_3776873 := by exact prefixLift 3776873
  have htrace : WordTrace (prefixWord ++ tailWord_3776873) baseStart_3776873 baseEnd_3776873 := by
    simpa [prefixWord, tailWord_3776873, baseEnd_3776873] using wordTrace_append hprefix tailTrace_3776873
  have hstable : (prefixWord ++ tailWord_3776873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776873).length < 2 ^ (prefixWord ++ tailWord_3776873).sum := by decide
  have hdescent : baseEnd_3776873 < baseStart_3776873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776903 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 3, 6]
def baseStart_3776903 : Nat := 118140960795 + 3776903 * 2 ^ 59
def prefixEnd_3776903 : Nat := 4983230072969 + 3 ^ 40 * 3776903 * 2
def baseEnd_3776903 : Nat := 646455541469447194447615

theorem tailTrace_3776903 : CollatzResearch.WordTrace tailWord_3776903 prefixEnd_3776903 646455541469447194447615 := by
  unfold tailWord_3776903
  simp only [CollatzResearch.WordTrace]
  refine ⟨137754969435932949522959363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91836646290621966348639575 137754969435932949522959363)
  ·
    refine ⟨206632454153899424284439045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137754969435932949522959363 206632454153899424284439045)
    ·
      refine ⟨38743585153856142053332321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206632454153899424284439045 38743585153856142053332321)
      ·
        refine ⟨29057688865392106539999241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38743585153856142053332321 29057688865392106539999241)
        ·
          refine ⟨21793266649044079904999431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29057688865392106539999241 21793266649044079904999431)
          ·
            refine ⟨32689899973566119857499147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21793266649044079904999431 32689899973566119857499147)
            ·
              refine ⟨49034849960349179786248721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32689899973566119857499147 49034849960349179786248721)
              ·
                refine ⟨36776137470261884839686541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49034849960349179786248721 36776137470261884839686541)
                ·
                  refine ⟨13791051551348206814882453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36776137470261884839686541 13791051551348206814882453)
                  ·
                    refine ⟨646455541469447194447615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13791051551348206814882453 646455541469447194447615)
                    ·
                      rfl

theorem cell23_3776903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_3776903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776903 prefixEnd_3776903 := by exact prefixLift 3776903
  have htrace : WordTrace (prefixWord ++ tailWord_3776903) baseStart_3776903 baseEnd_3776903 := by
    simpa [prefixWord, tailWord_3776903, baseEnd_3776903] using wordTrace_append hprefix tailTrace_3776903
  have hstable : (prefixWord ++ tailWord_3776903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776903).length < 2 ^ (prefixWord ++ tailWord_3776903).sum := by decide
  have hdescent : baseEnd_3776903 < baseStart_3776903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776904 : List Nat := [2, 1, 3, 3, 1, 1, 3, 4, 1, 1, 3]
def baseStart_3776904 : Nat := 118140960795 + 3776904 * 2 ^ 59
def prefixEnd_3776904 : Nat := 4983230072969 + 3 ^ 40 * 3776904 * 2
def baseEnd_3776904 : Nat := 1939367137888996079430341

theorem tailTrace_3776904 : CollatzResearch.WordTrace tailWord_3776904 prefixEnd_3776904 1939367137888996079430341 := by
  unfold tailWord_3776904
  simp only [CollatzResearch.WordTrace]
  refine ⟨68877502954464663346872883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91836670605952884462497177 68877502954464663346872883)
  ·
    refine ⟨103316254431696995020309325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68877502954464663346872883 103316254431696995020309325)
    ·
      refine ⟨38743595411886373132615997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103316254431696995020309325 38743595411886373132615997)
      ·
        refine ⟨14528848279457389924730999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38743595411886373132615997 14528848279457389924730999)
        ·
          refine ⟨21793272419186084887096499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14528848279457389924730999 21793272419186084887096499)
          ·
            refine ⟨32689908628779127330644749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21793272419186084887096499 32689908628779127330644749)
            ·
              refine ⟨12258715735792172748991781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32689908628779127330644749 12258715735792172748991781)
              ·
                refine ⟨2298509200461032390435959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12258715735792172748991781 2298509200461032390435959)
                ·
                  refine ⟨3447763800691548585653939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2298509200461032390435959 3447763800691548585653939)
                  ·
                    refine ⟨5171645701037322878480909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3447763800691548585653939 5171645701037322878480909)
                    ·
                      refine ⟨1939367137888996079430341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5171645701037322878480909 1939367137888996079430341)
                      ·
                        rfl

theorem cell23_3776904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_3776904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776904 prefixEnd_3776904 := by exact prefixLift 3776904
  have htrace : WordTrace (prefixWord ++ tailWord_3776904) baseStart_3776904 baseEnd_3776904 := by
    simpa [prefixWord, tailWord_3776904, baseEnd_3776904] using wordTrace_append hprefix tailTrace_3776904
  have hstable : (prefixWord ++ tailWord_3776904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776904).length < 2 ^ (prefixWord ++ tailWord_3776904).sum := by decide
  have hdescent : baseEnd_3776904 < baseStart_3776904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776913 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 3]
def baseStart_3776913 : Nat := 118140960795 + 3776913 * 2 ^ 59
def prefixEnd_3776913 : Nat := 4983230072969 + 3 ^ 40 * 3776913 * 2
def baseEnd_3776913 : Nat := 1939371759214886544217799

theorem tailTrace_3776913 : CollatzResearch.WordTrace tailWord_3776913 prefixEnd_3776913 1939371759214886544217799 := by
  unfold tailWord_3776913
  simp only [CollatzResearch.WordTrace]
  refine ⟨137755334165896721230823393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91836889443931147487215595 137755334165896721230823393)
  ·
    refine ⟨103316500624422540923117545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137755334165896721230823393 103316500624422540923117545)
    ·
      refine ⟨77487375468316905692338159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103316500624422540923117545 77487375468316905692338159)
      ·
        refine ⟨116231063202475358538507239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77487375468316905692338159 116231063202475358538507239)
        ·
          refine ⟨174346594803713037807760859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116231063202475358538507239 174346594803713037807760859)
          ·
            refine ⟨261519892205569556711641289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174346594803713037807760859 261519892205569556711641289)
            ·
              refine ⟨196139919154177167533730967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261519892205569556711641289 196139919154177167533730967)
              ·
                refine ⟨294209878731265751300596451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196139919154177167533730967 294209878731265751300596451)
                ·
                  refine ⟨441314818096898626950894677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294209878731265751300596451 441314818096898626950894677)
                  ·
                    refine ⟨5171658024573030784580797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 441314818096898626950894677 5171658024573030784580797)
                    ·
                      refine ⟨1939371759214886544217799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5171658024573030784580797 1939371759214886544217799)
                      ·
                        rfl

theorem cell23_3776913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 3].length) (baseStart_3776913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776913 prefixEnd_3776913 := by exact prefixLift 3776913
  have htrace : WordTrace (prefixWord ++ tailWord_3776913) baseStart_3776913 baseEnd_3776913 := by
    simpa [prefixWord, tailWord_3776913, baseEnd_3776913] using wordTrace_append hprefix tailTrace_3776913
  have hstable : (prefixWord ++ tailWord_3776913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776913).length < 2 ^ (prefixWord ++ tailWord_3776913).sum := by decide
  have hdescent : baseEnd_3776913 < baseStart_3776913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776920 : List Nat := [2, 1, 2, 5, 1, 1, 1, 3, 1, 6]
def baseStart_3776920 : Nat := 118140960795 + 3776920 * 2 ^ 59
def prefixEnd_3776920 : Nat := 4983230072969 + 3 ^ 40 * 3776920 * 2
def baseEnd_3776920 : Nat := 646458451193156005610089

theorem tailTrace_3776920 : CollatzResearch.WordTrace tailWord_3776920 prefixEnd_3776920 646458451193156005610089 := by
  unfold tailWord_3776920
  simp only [CollatzResearch.WordTrace]
  refine ⟨68877794738435680713164107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91837059651247574284218809 68877794738435680713164107)
  ·
    refine ⟨103316692107653521069746161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68877794738435680713164107 103316692107653521069746161)
    ·
      refine ⟨77487519080740140802309621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103316692107653521069746161 77487519080740140802309621)
      ·
        refine ⟨7264454913819388200216527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77487519080740140802309621 7264454913819388200216527)
        ·
          refine ⟨10896682370729082300324791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7264454913819388200216527 10896682370729082300324791)
          ·
            refine ⟨16345023556093623450487187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10896682370729082300324791 16345023556093623450487187)
            ·
              refine ⟨24517535334140435175730781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16345023556093623450487187 24517535334140435175730781)
              ·
                refine ⟨9194075750302663190899043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24517535334140435175730781 9194075750302663190899043)
                ·
                  refine ⟨13791113625453994786348565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9194075750302663190899043 13791113625453994786348565)
                  ·
                    refine ⟨646458451193156005610089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13791113625453994786348565 646458451193156005610089)
                    ·
                      rfl

theorem cell23_3776920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 1, 6].length) (baseStart_3776920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776920 prefixEnd_3776920 := by exact prefixLift 3776920
  have htrace : WordTrace (prefixWord ++ tailWord_3776920) baseStart_3776920 baseEnd_3776920 := by
    simpa [prefixWord, tailWord_3776920, baseEnd_3776920] using wordTrace_append hprefix tailTrace_3776920
  have hstable : (prefixWord ++ tailWord_3776920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776920).length < 2 ^ (prefixWord ++ tailWord_3776920).sum := by decide
  have hdescent : baseEnd_3776920 < baseStart_3776920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776941 : List Nat := [1, 5, 2, 2, 2, 2, 2, 1, 1, 5]
def baseStart_3776941 : Nat := 118140960795 + 3776941 * 2 ^ 59
def prefixEnd_3776941 : Nat := 4983230072969 + 3 ^ 40 * 3776941 * 2
def baseEnd_3776941 : Nat := 646462045557737478222557

theorem tailTrace_3776941 : CollatzResearch.WordTrace tailWord_3776941 prefixEnd_3776941 646462045557737478222557 := by
  unfold tailWord_3776941
  simp only [CollatzResearch.WordTrace]
  refine ⟨137756355409795282012842677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91837570273196854675228451 137756355409795282012842677)
  ·
    refine ⟨12914658319668307688704001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137756355409795282012842677 12914658319668307688704001)
    ·
      refine ⟨9685993739751230766528001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12914658319668307688704001 9685993739751230766528001)
      ·
        refine ⟨7264495304813423074896001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9685993739751230766528001 7264495304813423074896001)
        ·
          refine ⟨5448371478610067306172001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7264495304813423074896001 5448371478610067306172001)
          ·
            refine ⟨4086278608957550479629001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5448371478610067306172001 4086278608957550479629001)
            ·
              refine ⟨3064708956718162859721751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4086278608957550479629001 3064708956718162859721751)
              ·
                refine ⟨4597063435077244289582627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3064708956718162859721751 4597063435077244289582627)
                ·
                  refine ⟨6895595152615866434373941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4597063435077244289582627 6895595152615866434373941)
                  ·
                    refine ⟨646462045557737478222557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6895595152615866434373941 646462045557737478222557)
                    ·
                      rfl

theorem cell23_3776941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_3776941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776941 prefixEnd_3776941 := by exact prefixLift 3776941
  have htrace : WordTrace (prefixWord ++ tailWord_3776941) baseStart_3776941 baseEnd_3776941 := by
    simpa [prefixWord, tailWord_3776941, baseEnd_3776941] using wordTrace_append hprefix tailTrace_3776941
  have hstable : (prefixWord ++ tailWord_3776941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776941).length < 2 ^ (prefixWord ++ tailWord_3776941).sum := by decide
  have hdescent : baseEnd_3776941 < baseStart_3776941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776977 : List Nat := [1, 2, 2, 1, 2, 1, 1, 7, 2, 1, 3]
def baseStart_3776977 : Nat := 118140960795 + 3776977 * 2 ^ 59
def prefixEnd_3776977 : Nat := 4983230072969 + 3 ^ 40 * 3776977 * 2
def baseEnd_3776977 : Nat := 1939404621976774293817505

theorem tailTrace_3776977 : CollatzResearch.WordTrace tailWord_3776977 prefixEnd_3776977 1939404621976774293817505 := by
  unfold tailWord_3776977
  simp only [CollatzResearch.WordTrace]
  refine ⟨137757668437664860161153185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91838445625109906774102123 137757668437664860161153185)
  ·
    refine ⟨103318251328248645120864889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137757668437664860161153185 103318251328248645120864889)
    ·
      refine ⟨77488688496186483840648667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103318251328248645120864889 77488688496186483840648667)
      ·
        refine ⟨116233032744279725760973001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77488688496186483840648667 116233032744279725760973001)
        ·
          refine ⟨87174774558209794320729751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116233032744279725760973001 87174774558209794320729751)
          ·
            refine ⟨130762161837314691481094627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87174774558209794320729751 130762161837314691481094627)
            ·
              refine ⟨196143242755972037221641941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130762161837314691481094627 196143242755972037221641941)
              ·
                refine ⟨4597107252093094622382233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 196143242755972037221641941 4597107252093094622382233)
                ·
                  refine ⟨3447830439069820966786675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4597107252093094622382233 3447830439069820966786675)
                  ·
                    refine ⟨5171745658604731450180013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3447830439069820966786675 5171745658604731450180013)
                    ·
                      refine ⟨1939404621976774293817505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5171745658604731450180013 1939404621976774293817505)
                      ·
                        rfl

theorem cell23_3776977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 2, 1, 3].length) (baseStart_3776977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776977 prefixEnd_3776977 := by exact prefixLift 3776977
  have htrace : WordTrace (prefixWord ++ tailWord_3776977) baseStart_3776977 baseEnd_3776977 := by
    simpa [prefixWord, tailWord_3776977, baseEnd_3776977] using wordTrace_append hprefix tailTrace_3776977
  have hstable : (prefixWord ++ tailWord_3776977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776977).length < 2 ^ (prefixWord ++ tailWord_3776977).sum := by decide
  have hdescent : baseEnd_3776977 < baseStart_3776977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3776995 : List Nat := [1, 1, 1, 6, 4, 1, 1, 3, 1, 2, 2]
def baseStart_3776995 : Nat := 118140960795 + 3776995 * 2 ^ 59
def prefixEnd_3776995 : Nat := 4983230072969 + 3 ^ 40 * 3776995 * 2
def baseEnd_3776995 : Nat := 1939413864628555223392423

theorem tailTrace_3776995 : CollatzResearch.WordTrace tailWord_3776995 prefixEnd_3776995 1939413864628555223392423 := by
  unfold tailWord_3776995
  simp only [CollatzResearch.WordTrace]
  refine ⟨137758324951599649235308439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91838883301066432823538959 137758324951599649235308439)
  ·
    refine ⟨206637487427399473852962659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137758324951599649235308439 206637487427399473852962659)
    ·
      refine ⟨309956231141099210779443989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206637487427399473852962659 309956231141099210779443989)
      ·
        refine ⟨14529198334739025505286437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 309956231141099210779443989 14529198334739025505286437)
        ·
          refine ⟨2724224687763567282241207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14529198334739025505286437 2724224687763567282241207)
          ·
            refine ⟨4086337031645350923361811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2724224687763567282241207 4086337031645350923361811)
            ·
              refine ⟨6129505547468026385042717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4086337031645350923361811 6129505547468026385042717)
              ·
                refine ⟨2298564580300509894391019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6129505547468026385042717 2298564580300509894391019)
                ·
                  refine ⟨3447846870450764841586529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2298564580300509894391019 3447846870450764841586529)
                  ·
                    refine ⟨2585885152838073631189897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3447846870450764841586529 2585885152838073631189897)
                    ·
                      refine ⟨1939413864628555223392423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2585885152838073631189897 1939413864628555223392423)
                      ·
                        rfl

theorem cell23_3776995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_3776995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3776995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3776995 prefixEnd_3776995 := by exact prefixLift 3776995
  have htrace : WordTrace (prefixWord ++ tailWord_3776995) baseStart_3776995 baseEnd_3776995 := by
    simpa [prefixWord, tailWord_3776995, baseEnd_3776995] using wordTrace_append hprefix tailTrace_3776995
  have hstable : (prefixWord ++ tailWord_3776995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3776995).length < 2 ^ (prefixWord ++ tailWord_3776995).sum := by decide
  have hdescent : baseEnd_3776995 < baseStart_3776995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3776995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777020 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 2, 4, 3]
def baseStart_3777020 : Nat := 118140960795 + 3777020 * 2 ^ 59
def prefixEnd_3777020 : Nat := 4983230072969 + 3 ^ 40 * 3777020 * 2
def baseEnd_3777020 : Nat := 1939426701644917625579807

theorem tailTrace_3777020 : CollatzResearch.WordTrace tailWord_3777020 prefixEnd_3777020 1939426701644917625579807 := by
  unfold tailWord_3777020
  simp only [CollatzResearch.WordTrace]
  refine ⟨68879618388254539252484257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91839491184339385669979009 68879618388254539252484257)
  ·
    refine ⟨51659713791190904439363193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68879618388254539252484257 51659713791190904439363193)
    ·
      refine ⟨38744785343393178329522395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51659713791190904439363193 38744785343393178329522395)
      ·
        refine ⟨58117178015089767494283593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38744785343393178329522395 58117178015089767494283593)
        ·
          refine ⟨43587883511317325620712695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58117178015089767494283593 43587883511317325620712695)
          ·
            refine ⟨65381825266975988431069043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43587883511317325620712695 65381825266975988431069043)
            ·
              refine ⟨98072737900463982646603565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65381825266975988431069043 98072737900463982646603565)
              ·
                refine ⟨36777276712673993492476337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98072737900463982646603565 36777276712673993492476337)
                ·
                  refine ⟨27582957534505495119357253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36777276712673993492476337 27582957534505495119357253)
                  ·
                    refine ⟨5171804537719780334879485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27582957534505495119357253 5171804537719780334879485)
                    ·
                      refine ⟨1939426701644917625579807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5171804537719780334879485 1939426701644917625579807)
                      ·
                        rfl

theorem cell23_3777020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_3777020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777020 prefixEnd_3777020 := by exact prefixLift 3777020
  have htrace : WordTrace (prefixWord ++ tailWord_3777020) baseStart_3777020 baseEnd_3777020 := by
    simpa [prefixWord, tailWord_3777020, baseEnd_3777020] using wordTrace_append hprefix tailTrace_3777020
  have hstable : (prefixWord ++ tailWord_3777020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777020).length < 2 ^ (prefixWord ++ tailWord_3777020).sum := by decide
  have hdescent : baseEnd_3777020 < baseStart_3777020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777028 : List Nat := [2, 3, 2, 3, 1, 3, 2, 1, 2, 1, 3]
def baseStart_3777028 : Nat := 118140960795 + 3777028 * 2 ^ 59
def prefixEnd_3777028 : Nat := 4983230072969 + 3 ^ 40 * 3777028 * 2
def baseEnd_3777028 : Nat := 1939430809490153594279771

theorem tailTrace_3777028 : CollatzResearch.WordTrace tailWord_3777028 prefixEnd_3777028 1939430809490153594279771 := by
  unfold tailWord_3777028
  simp only [CollatzResearch.WordTrace]
  refine ⟨68879764280240047935629869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91839685706986730580839825 68879764280240047935629869)
  ·
    refine ⟨25829911605090017975861201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68879764280240047935629869 25829911605090017975861201)
    ·
      refine ⟨19372433703817513481895901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25829911605090017975861201 19372433703817513481895901)
      ·
        refine ⟨7264662638931567555710963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19372433703817513481895901 7264662638931567555710963)
        ·
          refine ⟨10896993958397351333566445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7264662638931567555710963 10896993958397351333566445)
          ·
            refine ⟨4086372734399006750087417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10896993958397351333566445 4086372734399006750087417)
            ·
              refine ⟨3064779550799255062565563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4086372734399006750087417 3064779550799255062565563)
              ·
                refine ⟨4597169326198882593848345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3064779550799255062565563 4597169326198882593848345)
                ·
                  refine ⟨3447876994649161945386259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4597169326198882593848345 3447876994649161945386259)
                  ·
                    refine ⟨5171815491973742918079389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3447876994649161945386259 5171815491973742918079389)
                    ·
                      refine ⟨1939430809490153594279771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5171815491973742918079389 1939430809490153594279771)
                      ·
                        rfl

theorem cell23_3777028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_3777028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777028 prefixEnd_3777028 := by exact prefixLift 3777028
  have htrace : WordTrace (prefixWord ++ tailWord_3777028) baseStart_3777028 baseEnd_3777028 := by
    simpa [prefixWord, tailWord_3777028, baseEnd_3777028] using wordTrace_append hprefix tailTrace_3777028
  have hstable : (prefixWord ++ tailWord_3777028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777028).length < 2 ^ (prefixWord ++ tailWord_3777028).sum := by decide
  have hdescent : baseEnd_3777028 < baseStart_3777028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777057 : List Nat := [1, 2, 3, 2, 2, 1, 2, 5, 5]
def baseStart_3777057 : Nat := 118140960795 + 3777057 * 2 ^ 59
def prefixEnd_3777057 : Nat := 4983230072969 + 3 ^ 40 * 3777057 * 2
def baseEnd_3777057 : Nat := 215493966714348220090793

theorem tailTrace_3777057 : CollatzResearch.WordTrace tailWord_3777057 prefixEnd_3777057 215493966714348220090793 := by
  unfold tailWord_3777057
  simp only [CollatzResearch.WordTrace]
  refine ⟨137760586277375033824065425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91840390851583355882710283 137760586277375033824065425)
  ·
    refine ⟨103320439708031275368049069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137760586277375033824065425 103320439708031275368049069)
    ·
      refine ⟨38745164890511728263018401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103320439708031275368049069 38745164890511728263018401)
      ·
        refine ⟨29058873667883796197263801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38745164890511728263018401 29058873667883796197263801)
        ·
          refine ⟨21794155250912847147947851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29058873667883796197263801 21794155250912847147947851)
          ·
            refine ⟨32691232876369270721921777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21794155250912847147947851 32691232876369270721921777)
            ·
              refine ⟨24518424657276953041441333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32691232876369270721921777 24518424657276953041441333)
              ·
                refine ⟨2298602311619714347635125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24518424657276953041441333 2298602311619714347635125)
                ·
                  refine ⟨215493966714348220090793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2298602311619714347635125 215493966714348220090793)
                  ·
                    rfl

theorem cell23_3777057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 5, 5].length) (baseStart_3777057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777057 prefixEnd_3777057 := by exact prefixLift 3777057
  have htrace : WordTrace (prefixWord ++ tailWord_3777057) baseStart_3777057 baseEnd_3777057 := by
    simpa [prefixWord, tailWord_3777057, baseEnd_3777057] using wordTrace_append hprefix tailTrace_3777057
  have hstable : (prefixWord ++ tailWord_3777057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777057).length < 2 ^ (prefixWord ++ tailWord_3777057).sum := by decide
  have hdescent : baseEnd_3777057 < baseStart_3777057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777074 : List Nat := [3, 2, 1, 1, 2, 1, 6, 2, 5]
def baseStart_3777074 : Nat := 118140960795 + 3777074 * 2 ^ 59
def prefixEnd_3777074 : Nat := 4983230072969 + 3 ^ 40 * 3777074 * 2
def baseEnd_3777074 : Nat := 215494936622251157144951

theorem tailTrace_3777074 : CollatzResearch.WordTrace tailWord_3777074 prefixEnd_3777074 215494936622251157144951 := by
  unfold tailWord_3777074
  simp only [CollatzResearch.WordTrace]
  refine ⟨34440301579578361431858569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91840804212208963818289517 34440301579578361431858569)
  ·
    refine ⟨25830226184683771073893927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34440301579578361431858569 25830226184683771073893927)
    ·
      refine ⟨38745339277025656610840891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25830226184683771073893927 38745339277025656610840891)
      ·
        refine ⟨58118008915538484916261337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38745339277025656610840891 58118008915538484916261337)
        ·
          refine ⟨43588506686653863687196003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58118008915538484916261337 43588506686653863687196003)
          ·
            refine ⟨65382760029980795530794005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43588506686653863687196003 65382760029980795530794005)
            ·
              refine ⟨3064816876405349790505969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 65382760029980795530794005 3064816876405349790505969)
              ·
                refine ⟨2298612657304012342879477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3064816876405349790505969 2298612657304012342879477)
                ·
                  refine ⟨215494936622251157144951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2298612657304012342879477 215494936622251157144951)
                  ·
                    rfl

theorem cell23_3777074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 2, 5].length) (baseStart_3777074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777074 prefixEnd_3777074 := by exact prefixLift 3777074
  have htrace : WordTrace (prefixWord ++ tailWord_3777074) baseStart_3777074 baseEnd_3777074 := by
    simpa [prefixWord, tailWord_3777074, baseEnd_3777074] using wordTrace_append hprefix tailTrace_3777074
  have hstable : (prefixWord ++ tailWord_3777074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777074).length < 2 ^ (prefixWord ++ tailWord_3777074).sum := by decide
  have hdescent : baseEnd_3777074 < baseStart_3777074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777077 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 1, 7, 2]
def baseStart_3777077 : Nat := 118140960795 + 3777077 * 2 ^ 59
def prefixEnd_3777077 : Nat := 4983230072969 + 3 ^ 40 * 3777077 * 2
def baseEnd_3777077 : Nat := 1939455970042223902567045

theorem tailTrace_3777077 : CollatzResearch.WordTrace tailWord_3777077 prefixEnd_3777077 1939455970042223902567045 := by
  unfold tailWord_3777077
  simp only [CollatzResearch.WordTrace]
  refine ⟨137761315737302577239793485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91840877158201718159862323 137761315737302577239793485)
  ·
    refine ⟨51660493401488466464922557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137761315737302577239793485 51660493401488466464922557)
    ·
      refine ⟨19372685025558174924345959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51660493401488466464922557 19372685025558174924345959)
      ·
        refine ⟨29059027538337262386518939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19372685025558174924345959 29059027538337262386518939)
        ·
          refine ⟨43588541307505893579778409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29059027538337262386518939 43588541307505893579778409)
          ·
            refine ⟨32691405980629420184833807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43588541307505893579778409 32691405980629420184833807)
            ·
              refine ⟨49037108970944130277250711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32691405980629420184833807 49037108970944130277250711)
              ·
                refine ⟨73555663456416195415876067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49037108970944130277250711 73555663456416195415876067)
                ·
                  refine ⟨110333495184624293123814101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73555663456416195415876067 110333495184624293123814101)
                  ·
                    refine ⟨2585941293389631870089393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 110333495184624293123814101 2585941293389631870089393)
                    ·
                      refine ⟨1939455970042223902567045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2585941293389631870089393 1939455970042223902567045)
                      ·
                        rfl

theorem cell23_3777077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_3777077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777077 prefixEnd_3777077 := by exact prefixLift 3777077
  have htrace : WordTrace (prefixWord ++ tailWord_3777077) baseStart_3777077 baseEnd_3777077 := by
    simpa [prefixWord, tailWord_3777077, baseEnd_3777077] using wordTrace_append hprefix tailTrace_3777077
  have hstable : (prefixWord ++ tailWord_3777077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777077).length < 2 ^ (prefixWord ++ tailWord_3777077).sum := by decide
  have hdescent : baseEnd_3777077 < baseStart_3777077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777080 : List Nat := [2, 1, 2, 1, 4, 1, 1, 3, 1, 2, 5]
def baseStart_3777080 : Nat := 118140960795 + 3777080 * 2 ^ 59
def prefixEnd_3777080 : Nat := 4983230072969 + 3 ^ 40 * 3777080 * 2
def baseEnd_3777080 : Nat := 1939457510484187390829531

theorem tailTrace_3777080 : CollatzResearch.WordTrace tailWord_3777080 prefixEnd_3777080 1939457510484187390829531 := by
  unfold tailWord_3777080
  simp only [CollatzResearch.WordTrace]
  refine ⟨68880712578145854376076347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91840950104194472501435129 68880712578145854376076347)
  ·
    refine ⟨103321068867218781564114521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68880712578145854376076347 103321068867218781564114521)
    ·
      refine ⟨77490801650414086173085891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103321068867218781564114521 77490801650414086173085891)
      ·
        refine ⟨116236202475621129259628837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77490801650414086173085891 116236202475621129259628837)
        ·
          refine ⟨21794287964178961736180407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116236202475621129259628837 21794287964178961736180407)
          ·
            refine ⟨32691431946268442604270611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21794287964178961736180407 32691431946268442604270611)
            ·
              refine ⟨49037147919402663906405917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32691431946268442604270611 49037147919402663906405917)
              ·
                refine ⟨18388930469775998964902219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49037147919402663906405917 18388930469775998964902219)
                ·
                  refine ⟨27583395704663998447353329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18388930469775998964902219 27583395704663998447353329)
                  ·
                    refine ⟨20687546778497998835514997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27583395704663998447353329 20687546778497998835514997)
                    ·
                      refine ⟨1939457510484187390829531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20687546778497998835514997 1939457510484187390829531)
                      ·
                        rfl

theorem cell23_3777080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_3777080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777080 prefixEnd_3777080 := by exact prefixLift 3777080
  have htrace : WordTrace (prefixWord ++ tailWord_3777080) baseStart_3777080 baseEnd_3777080 := by
    simpa [prefixWord, tailWord_3777080, baseEnd_3777080] using wordTrace_append hprefix tailTrace_3777080
  have hstable : (prefixWord ++ tailWord_3777080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777080).length < 2 ^ (prefixWord ++ tailWord_3777080).sum := by decide
  have hdescent : baseEnd_3777080 < baseStart_3777080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777120 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 6]
def baseStart_3777120 : Nat := 118140960795 + 3777120 * 2 ^ 59
def prefixEnd_3777120 : Nat := 4983230072969 + 3 ^ 40 * 3777120 * 2
def baseEnd_3777120 : Nat := 1939478049710367234329347

theorem tailTrace_3777120 : CollatzResearch.WordTrace tailWord_3777120 prefixEnd_3777120 1939478049710367234329347 := by
  unfold tailWord_3777120
  simp only [CollatzResearch.WordTrace]
  refine ⟨68881442038073397791804407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91841922717431197055739209 68881442038073397791804407)
  ·
    refine ⟨103322163057110096687706611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68881442038073397791804407 103322163057110096687706611)
    ·
      refine ⟨154983244585665145031559917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103322163057110096687706611 154983244585665145031559917)
      ·
        refine ⟨58118716719624429386834969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154983244585665145031559917 58118716719624429386834969)
        ·
          refine ⟨43589037539718322040126227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58118716719624429386834969 43589037539718322040126227)
          ·
            refine ⟨65383556309577483060189341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43589037539718322040126227 65383556309577483060189341)
            ·
              refine ⟨24518833616091556147571003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65383556309577483060189341 24518833616091556147571003)
              ·
                refine ⟨36778250424137334221356505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24518833616091556147571003 36778250424137334221356505)
                ·
                  refine ⟨27583687818103000666017379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36778250424137334221356505 27583687818103000666017379)
                  ·
                    refine ⟨41375531727154500999026069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27583687818103000666017379 41375531727154500999026069)
                    ·
                      refine ⟨1939478049710367234329347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41375531727154500999026069 1939478049710367234329347)
                      ·
                        rfl

theorem cell23_3777120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_3777120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777120 prefixEnd_3777120 := by exact prefixLift 3777120
  have htrace : WordTrace (prefixWord ++ tailWord_3777120) baseStart_3777120 baseEnd_3777120 := by
    simpa [prefixWord, tailWord_3777120, baseEnd_3777120] using wordTrace_append hprefix tailTrace_3777120
  have hstable : (prefixWord ++ tailWord_3777120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777120).length < 2 ^ (prefixWord ++ tailWord_3777120).sum := by decide
  have hdescent : baseEnd_3777120 < baseStart_3777120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777127 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 4, 2, 3]
def baseStart_3777127 : Nat := 118140960795 + 3777127 * 2 ^ 59
def prefixEnd_3777127 : Nat := 4983230072969 + 3 ^ 40 * 3777127 * 2
def baseEnd_3777127 : Nat := 1939481644074948706941815

theorem tailTrace_3777127 : CollatzResearch.WordTrace tailWord_3777127 prefixEnd_3777127 1939481644074948706941815 := by
  unfold tailWord_3777127
  simp only [CollatzResearch.WordTrace]
  refine ⟨137763139387121435779113635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91842092924747623852742423 137763139387121435779113635)
  ·
    refine ⟨206644709080682153668670453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137763139387121435779113635 206644709080682153668670453)
    ·
      refine ⟨19372941476313951906437855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 206644709080682153668670453 19372941476313951906437855)
      ·
        refine ⟨29059412214470927859656783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19372941476313951906437855 29059412214470927859656783)
        ·
          refine ⟨43589118321706391789485175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29059412214470927859656783 43589118321706391789485175)
          ·
            refine ⟨65383677482559587684227763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43589118321706391789485175 65383677482559587684227763)
            ·
              refine ⟨98075516223839381526341645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65383677482559587684227763 98075516223839381526341645)
              ·
                refine ⟨36778318583939768072378117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98075516223839381526341645 36778318583939768072378117)
                ·
                  refine ⟨6895934734488706513570897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36778318583939768072378117 6895934734488706513570897)
                  ·
                    refine ⟨5171951050866529885178173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6895934734488706513570897 5171951050866529885178173)
                    ·
                      refine ⟨1939481644074948706941815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5171951050866529885178173 1939481644074948706941815)
                      ·
                        rfl

theorem cell23_3777127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_3777127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777127 prefixEnd_3777127 := by exact prefixLift 3777127
  have htrace : WordTrace (prefixWord ++ tailWord_3777127) baseStart_3777127 baseEnd_3777127 := by
    simpa [prefixWord, tailWord_3777127, baseEnd_3777127] using wordTrace_append hprefix tailTrace_3777127
  have hstable : (prefixWord ++ tailWord_3777127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777127).length < 2 ^ (prefixWord ++ tailWord_3777127).sum := by decide
  have hdescent : baseEnd_3777127 < baseStart_3777127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777134 : List Nat := [4, 1, 2, 2, 2, 1, 1, 3, 3, 4]
def baseStart_3777134 : Nat := 118140960795 + 3777134 * 2 ^ 59
def prefixEnd_3777134 : Nat := 4983230072969 + 3 ^ 40 * 3777134 * 2
def baseEnd_3777134 : Nat := 646495079479843393184761

theorem tailTrace_3777134 : CollatzResearch.WordTrace tailWord_3777134 prefixEnd_3777134 646495079479843393184761 := by
  unfold tailWord_3777134
  simp only [CollatzResearch.WordTrace]
  refine ⟨17220424337262009496827307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91842263132064050649745637 17220424337262009496827307)
  ·
    refine ⟨25830636505893014245240961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17220424337262009496827307 25830636505893014245240961)
    ·
      refine ⟨19372977379419760683930721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25830636505893014245240961 19372977379419760683930721)
      ·
        refine ⟨14529733034564820512948041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19372977379419760683930721 14529733034564820512948041)
        ·
          refine ⟨10897299775923615384711031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14529733034564820512948041 10897299775923615384711031)
          ·
            refine ⟨16345949663885423077066547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10897299775923615384711031 16345949663885423077066547)
            ·
              refine ⟨24518924495828134615599821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16345949663885423077066547 24518924495828134615599821)
              ·
                refine ⟨9194596685935550480849933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24518924495828134615599821 9194596685935550480849933)
                ·
                  refine ⟨3447973757225831430318725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9194596685935550480849933 3447973757225831430318725)
                  ·
                    refine ⟨646495079479843393184761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3447973757225831430318725 646495079479843393184761)
                    ·
                      rfl

theorem cell23_3777134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_3777134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777134 prefixEnd_3777134 := by exact prefixLift 3777134
  have htrace : WordTrace (prefixWord ++ tailWord_3777134) baseStart_3777134 baseEnd_3777134 := by
    simpa [prefixWord, tailWord_3777134, baseEnd_3777134] using wordTrace_append hprefix tailTrace_3777134
  have hstable : (prefixWord ++ tailWord_3777134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777134).length < 2 ^ (prefixWord ++ tailWord_3777134).sum := by decide
  have hdescent : baseEnd_3777134 < baseStart_3777134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777177 : List Nat := [1, 2, 1, 2, 1, 2, 3, 5, 1, 5]
def baseStart_3777177 : Nat := 118140960795 + 3777177 * 2 ^ 59
def prefixEnd_3777177 : Nat := 4983230072969 + 3 ^ 40 * 3777177 * 2
def baseEnd_3777177 : Nat := 646502439369224503772195

theorem tailTrace_3777177 : CollatzResearch.WordTrace tailWord_3777177 prefixEnd_3777177 646502439369224503772195 := by
  unfold tailWord_3777177
  simp only [CollatzResearch.WordTrace]
  refine ⟨137764963036940294318433785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91843308691293529545622523 137764963036940294318433785)
  ·
    refine ⟨103323722277705220738825339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137764963036940294318433785 103323722277705220738825339)
    ·
      refine ⟨154985583416557831108238009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103323722277705220738825339 154985583416557831108238009)
      ·
        refine ⟨116239187562418373331178507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154985583416557831108238009 116239187562418373331178507)
        ·
          refine ⟨174358781343627559996767761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116239187562418373331178507 174358781343627559996767761)
          ·
            refine ⟨130769086007720669997575821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174358781343627559996767761 130769086007720669997575821)
            ·
              refine ⟨49038407252895251249090933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130769086007720669997575821 49038407252895251249090933)
              ·
                refine ⟨4597350679958929804602275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49038407252895251249090933 4597350679958929804602275)
                ·
                  refine ⟨6896026019938394706903413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4597350679958929804602275 6896026019938394706903413)
                  ·
                    refine ⟨646502439369224503772195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6896026019938394706903413 646502439369224503772195)
                    ·
                      rfl

theorem cell23_3777177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 5].length) (baseStart_3777177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777177 prefixEnd_3777177 := by exact prefixLift 3777177
  have htrace : WordTrace (prefixWord ++ tailWord_3777177) baseStart_3777177 baseEnd_3777177 := by
    simpa [prefixWord, tailWord_3777177, baseEnd_3777177] using wordTrace_append hprefix tailTrace_3777177
  have hstable : (prefixWord ++ tailWord_3777177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777177).length < 2 ^ (prefixWord ++ tailWord_3777177).sum := by decide
  have hdescent : baseEnd_3777177 < baseStart_3777177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777198 : List Nat := [4, 1, 4, 1, 1, 3, 2, 1, 6]
def baseStart_3777198 : Nat := 118140960795 + 3777198 * 2 ^ 59
def prefixEnd_3777198 : Nat := 4983230072969 + 3 ^ 40 * 3777198 * 2
def baseEnd_3777198 : Nat := 215502011244601992128221

theorem tailTrace_3777198 : CollatzResearch.WordTrace tailWord_3777198 prefixEnd_3777198 215502011244601992128221 := by
  unfold tailWord_3777198
  simp only [CollatzResearch.WordTrace]
  refine ⟨17220716121233026863118531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91843819313242809936632165 17220716121233026863118531)
  ·
    refine ⟨25831074181849540294677797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17220716121233026863118531 25831074181849540294677797)
    ·
      refine ⟨4843326409096788805252087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25831074181849540294677797 4843326409096788805252087)
      ·
        refine ⟨7264989613645183207878131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4843326409096788805252087 7264989613645183207878131)
        ·
          refine ⟨10897484420467774811817197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7264989613645183207878131 10897484420467774811817197)
          ·
            refine ⟨4086556657675415554431449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10897484420467774811817197 4086556657675415554431449)
            ·
              refine ⟨3064917493256561665823587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4086556657675415554431449 3064917493256561665823587)
              ·
                refine ⟨4597376239884842498735381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3064917493256561665823587 4597376239884842498735381)
                ·
                  refine ⟨215502011244601992128221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4597376239884842498735381 215502011244601992128221)
                  ·
                    rfl

theorem cell23_3777198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 6].length) (baseStart_3777198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777198 prefixEnd_3777198 := by exact prefixLift 3777198
  have htrace : WordTrace (prefixWord ++ tailWord_3777198) baseStart_3777198 baseEnd_3777198 := by
    simpa [prefixWord, tailWord_3777198, baseEnd_3777198] using wordTrace_append hprefix tailTrace_3777198
  have hstable : (prefixWord ++ tailWord_3777198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777198).length < 2 ^ (prefixWord ++ tailWord_3777198).sum := by decide
  have hdescent : baseEnd_3777198 < baseStart_3777198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777214 : List Nat := [4, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4]
def baseStart_3777214 : Nat := 118140960795 + 3777214 * 2 ^ 59
def prefixEnd_3777214 : Nat := 4983230072969 + 3 ^ 40 * 3777214 * 2
def baseEnd_3777214 : Nat := 1939526316891889866553915

theorem tailTrace_3777214 : CollatzResearch.WordTrace tailWord_3777214 prefixEnd_3777214 1939526316891889866553915 := by
  unfold tailWord_3777214
  simp only [CollatzResearch.WordTrace]
  refine ⟨17220789067225781204691337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91844208358537499758353797 17220789067225781204691337)
  ·
    refine ⟨12915591800419335903518503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17220789067225781204691337 12915591800419335903518503)
    ·
      refine ⟨19373387700629003855277755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12915591800419335903518503 19373387700629003855277755)
      ·
        refine ⟨29060081550943505782916633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19373387700629003855277755 29060081550943505782916633)
        ·
          refine ⟨21795061163207629337187475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29060081550943505782916633 21795061163207629337187475)
          ·
            refine ⟨32692591744811444005781213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21795061163207629337187475 32692591744811444005781213)
            ·
              refine ⟨12259721904304291502167955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32692591744811444005781213 12259721904304291502167955)
              ·
                refine ⟨18389582856456437253251933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12259721904304291502167955 18389582856456437253251933)
                ·
                  refine ⟨6896093571171163969969475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18389582856456437253251933 6896093571171163969969475)
                  ·
                    refine ⟨10344140356756745954954213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6896093571171163969969475 10344140356756745954954213)
                    ·
                      refine ⟨1939526316891889866553915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10344140356756745954954213 1939526316891889866553915)
                      ·
                        rfl

theorem cell23_3777214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_3777214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777214 prefixEnd_3777214 := by exact prefixLift 3777214
  have htrace : WordTrace (prefixWord ++ tailWord_3777214) baseStart_3777214 baseEnd_3777214 := by
    simpa [prefixWord, tailWord_3777214, baseEnd_3777214] using wordTrace_append hprefix tailTrace_3777214
  have hstable : (prefixWord ++ tailWord_3777214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777214).length < 2 ^ (prefixWord ++ tailWord_3777214).sum := by decide
  have hdescent : baseEnd_3777214 < baseStart_3777214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777237 : List Nat := [1, 3, 2, 5, 12]
def baseStart_3777237 : Nat := 118140960795 + 3777237 * 2 ^ 59
def prefixEnd_3777237 : Nat := 4983230072969 + 3 ^ 40 * 3777237 * 2
def baseEnd_3777237 : Nat := 2660546127499236319021

theorem tailTrace_3777237 : CollatzResearch.WordTrace tailWord_3777237 prefixEnd_3777237 2660546127499236319021 := by
  unfold tailWord_3777237
  simp only [CollatzResearch.WordTrace]
  refine ⟨137767151416722924565617965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91844767611148616377078643 137767151416722924565617965)
  ·
    refine ⟨51662681781271096712106737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137767151416722924565617965 51662681781271096712106737)
    ·
      refine ⟨38747011335953322534080053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51662681781271096712106737 38747011335953322534080053)
      ·
        refine ⟨3632532312745623987570005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38747011335953322534080053 3632532312745623987570005)
        ·
          refine ⟨2660546127499236319021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3632532312745623987570005 2660546127499236319021)
          ·
            rfl

theorem cell23_3777237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 12].length) (baseStart_3777237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777237 prefixEnd_3777237 := by exact prefixLift 3777237
  have htrace : WordTrace (prefixWord ++ tailWord_3777237) baseStart_3777237 baseEnd_3777237 := by
    simpa [prefixWord, tailWord_3777237, baseEnd_3777237] using wordTrace_append hprefix tailTrace_3777237
  have hstable : (prefixWord ++ tailWord_3777237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777237).length < 2 ^ (prefixWord ++ tailWord_3777237).sum := by decide
  have hdescent : baseEnd_3777237 < baseStart_3777237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777264 : List Nat := [2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 3]
def baseStart_3777264 : Nat := 118140960795 + 3777264 * 2 ^ 59
def prefixEnd_3777264 : Nat := 4983230072969 + 3 ^ 40 * 3777264 * 2
def baseEnd_3777264 : Nat := 1939551990924614670928685

theorem tailTrace_3777264 : CollatzResearch.WordTrace tailWord_3777264 prefixEnd_3777264 1939551990924614670928685 := by
  unfold tailWord_3777264
  simp only [CollatzResearch.WordTrace]
  refine ⟨68884068093812554088425423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91845424125083405451233897 68884068093812554088425423)
  ·
    refine ⟨103326102140718831132638135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68884068093812554088425423 103326102140718831132638135)
    ·
      refine ⟨154989153211078246698957203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103326102140718831132638135 154989153211078246698957203)
      ·
        refine ⟨232483729816617370048435805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154989153211078246698957203 232483729816617370048435805)
        ·
          refine ⟨87181398681231513768163427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232483729816617370048435805 87181398681231513768163427)
          ·
            refine ⟨130772098021847270652245141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87181398681231513768163427 130772098021847270652245141)
            ·
              refine ⟨6129942094774090811823991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 130772098021847270652245141 6129942094774090811823991)
              ·
                refine ⟨9194913142161136217735987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6129942094774090811823991 9194913142161136217735987)
                ·
                  refine ⟨13792369713241704326603981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9194913142161136217735987 13792369713241704326603981)
                  ·
                    refine ⟨5172138642465639122476493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13792369713241704326603981 5172138642465639122476493)
                    ·
                      refine ⟨1939551990924614670928685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5172138642465639122476493 1939551990924614670928685)
                      ·
                        rfl

theorem cell23_3777264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 3].length) (baseStart_3777264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777264 prefixEnd_3777264 := by exact prefixLift 3777264
  have htrace : WordTrace (prefixWord ++ tailWord_3777264) baseStart_3777264 baseEnd_3777264 := by
    simpa [prefixWord, tailWord_3777264, baseEnd_3777264] using wordTrace_append hprefix tailTrace_3777264
  have hstable : (prefixWord ++ tailWord_3777264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777264).length < 2 ^ (prefixWord ++ tailWord_3777264).sum := by decide
  have hdescent : baseEnd_3777264 < baseStart_3777264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777269 : List Nat := [1, 3, 6, 1, 2, 1, 1, 1, 2, 3, 2]
def baseStart_3777269 : Nat := 118140960795 + 3777269 * 2 ^ 59
def prefixEnd_3777269 : Nat := 4983230072969 + 3 ^ 40 * 3777269 * 2
def baseEnd_3777269 : Nat := 1939554558327887151366163

theorem tailTrace_3777269 : CollatzResearch.WordTrace tailWord_3777269 prefixEnd_3777269 1939554558327887151366163 := by
  unfold tailWord_3777269
  simp only [CollatzResearch.WordTrace]
  refine ⟨137768318552606994030782861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91845545701737996020521907 137768318552606994030782861)
  ·
    refine ⟨51663119457227622761543573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137768318552606994030782861 51663119457227622761543573)
    ·
      refine ⟨2421708724557544816947355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51663119457227622761543573 2421708724557544816947355)
      ·
        refine ⟨3632563086836317225421033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2421708724557544816947355 3632563086836317225421033)
        ·
          refine ⟨2724422315127237919065775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3632563086836317225421033 2724422315127237919065775)
          ·
            refine ⟨4086633472690856878598663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2724422315127237919065775 4086633472690856878598663)
            ·
              refine ⟨6129950209036285317897995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4086633472690856878598663 6129950209036285317897995)
              ·
                refine ⟨9194925313554427976846993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6129950209036285317897995 9194925313554427976846993)
                ·
                  refine ⟨6896193985165820982635245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9194925313554427976846993 6896193985165820982635245)
                  ·
                    refine ⟨2586072744437182868488217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6896193985165820982635245 2586072744437182868488217)
                    ·
                      refine ⟨1939554558327887151366163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2586072744437182868488217 1939554558327887151366163)
                      ·
                        rfl

theorem cell23_3777269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_3777269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777269 prefixEnd_3777269 := by exact prefixLift 3777269
  have htrace : WordTrace (prefixWord ++ tailWord_3777269) baseStart_3777269 baseEnd_3777269 := by
    simpa [prefixWord, tailWord_3777269, baseEnd_3777269] using wordTrace_append hprefix tailTrace_3777269
  have hstable : (prefixWord ++ tailWord_3777269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777269).length < 2 ^ (prefixWord ++ tailWord_3777269).sum := by decide
  have hdescent : baseEnd_3777269 < baseStart_3777269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777277 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 2, 2, 5]
def baseStart_3777277 : Nat := 118140960795 + 3777277 * 2 ^ 59
def prefixEnd_3777277 : Nat := 4983230072969 + 3 ^ 40 * 3777277 * 2
def baseEnd_3777277 : Nat := 1939558666173123120066125

theorem tailTrace_3777277 : CollatzResearch.WordTrace tailWord_3777277 prefixEnd_3777277 1939558666173123120066125 := by
  unfold tailWord_3777277
  simp only [CollatzResearch.WordTrace]
  refine ⟨137768610336578011397074085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91845740224385340931382723 137768610336578011397074085)
  ·
    refine ⟨25831614438108377136951391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137768610336578011397074085 25831614438108377136951391)
    ·
      refine ⟨38747421657162565705427087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25831614438108377136951391 38747421657162565705427087)
      ·
        refine ⟨58121132485743848558140631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38747421657162565705427087 58121132485743848558140631)
        ·
          refine ⟨87181698728615772837210947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58121132485743848558140631 87181698728615772837210947)
          ·
            refine ⟨130772548092923659255816421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87181698728615772837210947 130772548092923659255816421)
            ·
              refine ⟨24519852767423186110465579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130772548092923659255816421 24519852767423186110465579)
              ·
                refine ⟨36779779151134779165698369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24519852767423186110465579 36779779151134779165698369)
                ·
                  refine ⟨27584834363351084374273777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36779779151134779165698369 27584834363351084374273777)
                  ·
                    refine ⟨20688625772513313280705333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27584834363351084374273777 20688625772513313280705333)
                    ·
                      refine ⟨1939558666173123120066125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20688625772513313280705333 1939558666173123120066125)
                      ·
                        rfl

theorem cell23_3777277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_3777277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777277 prefixEnd_3777277 := by exact prefixLift 3777277
  have htrace : WordTrace (prefixWord ++ tailWord_3777277) baseStart_3777277 baseEnd_3777277 := by
    simpa [prefixWord, tailWord_3777277, baseEnd_3777277] using wordTrace_append hprefix tailTrace_3777277
  have hstable : (prefixWord ++ tailWord_3777277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777277).length < 2 ^ (prefixWord ++ tailWord_3777277).sum := by decide
  have hdescent : baseEnd_3777277 < baseStart_3777277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777282 : List Nat := [3, 4, 1, 1, 1, 3, 2, 3, 1, 2, 2]
def baseStart_3777282 : Nat := 118140960795 + 3777282 * 2 ^ 59
def prefixEnd_3777282 : Nat := 4983230072969 + 3 ^ 40 * 3777282 * 2
def baseEnd_3777282 : Nat := 1939561233576395600503603

theorem tailTrace_3777282 : CollatzResearch.WordTrace tailWord_3777282 prefixEnd_3777282 1939561233576395600503603 := by
  unfold tailWord_3777282
  simp only [CollatzResearch.WordTrace]
  refine ⟨34442198175389974312751525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91845861801039931500670733 34442198175389974312751525)
  ·
    refine ⟨6457912157885620183640911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34442198175389974312751525 6457912157885620183640911)
    ·
      refine ⟨9686868236828430275461367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6457912157885620183640911 9686868236828430275461367)
      ·
        refine ⟨14530302355242645413192051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9686868236828430275461367 14530302355242645413192051)
        ·
          refine ⟨21795453532863968119788077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14530302355242645413192051 21795453532863968119788077)
          ·
            refine ⟨8173295074823988044920529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21795453532863968119788077 8173295074823988044920529)
            ·
              refine ⟨6129971306117991033690397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8173295074823988044920529 6129971306117991033690397)
              ·
                refine ⟨2298739239794246637633899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6129971306117991033690397 2298739239794246637633899)
                ·
                  refine ⟨3448108859691369956450849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2298739239794246637633899 3448108859691369956450849)
                  ·
                    refine ⟨2586081644768527467338137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3448108859691369956450849 2586081644768527467338137)
                    ·
                      refine ⟨1939561233576395600503603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2586081644768527467338137 1939561233576395600503603)
                      ·
                        rfl

theorem cell23_3777282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_3777282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777282 prefixEnd_3777282 := by exact prefixLift 3777282
  have htrace : WordTrace (prefixWord ++ tailWord_3777282) baseStart_3777282 baseEnd_3777282 := by
    simpa [prefixWord, tailWord_3777282, baseEnd_3777282] using wordTrace_append hprefix tailTrace_3777282
  have hstable : (prefixWord ++ tailWord_3777282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777282).length < 2 ^ (prefixWord ++ tailWord_3777282).sum := by decide
  have hdescent : baseEnd_3777282 < baseStart_3777282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777297 : List Nat := [1, 2, 2, 1, 1, 3, 3, 2, 2, 6]
def baseStart_3777297 : Nat := 118140960795 + 3777297 * 2 ^ 59
def prefixEnd_3777297 : Nat := 4983230072969 + 3 ^ 40 * 3777297 * 2
def baseEnd_3777297 : Nat := 646522978595404347272011

theorem tailTrace_3777297 : CollatzResearch.WordTrace tailWord_3777297 prefixEnd_3777297 646522978595404347272011 := by
  unfold tailWord_3777297
  simp only [CollatzResearch.WordTrace]
  refine ⟨137769339796505554812802145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91846226531003703208534763 137769339796505554812802145)
  ·
    refine ⟨103327004847379166109601609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137769339796505554812802145 103327004847379166109601609)
    ·
      refine ⟨77495253635534374582201207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103327004847379166109601609 77495253635534374582201207)
      ·
        refine ⟨116242880453301561873301811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77495253635534374582201207 116242880453301561873301811)
        ·
          refine ⟨174364320679952342809952717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116242880453301561873301811 174364320679952342809952717)
          ·
            refine ⟨65386620254982128553732269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174364320679952342809952717 65386620254982128553732269)
            ·
              refine ⟨24519982595618298207649601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65386620254982128553732269 24519982595618298207649601)
              ·
                refine ⟨18389986946713723655737201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24519982595618298207649601 18389986946713723655737201)
                ·
                  refine ⟨13792490210035292741802901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18389986946713723655737201 13792490210035292741802901)
                  ·
                    refine ⟨646522978595404347272011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13792490210035292741802901 646522978595404347272011)
                    ·
                      rfl

theorem cell23_3777297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 6].length) (baseStart_3777297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777297 prefixEnd_3777297 := by exact prefixLift 3777297
  have htrace : WordTrace (prefixWord ++ tailWord_3777297) baseStart_3777297 baseEnd_3777297 := by
    simpa [prefixWord, tailWord_3777297, baseEnd_3777297] using wordTrace_append hprefix tailTrace_3777297
  have hstable : (prefixWord ++ tailWord_3777297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777297).length < 2 ^ (prefixWord ++ tailWord_3777297).sum := by decide
  have hdescent : baseEnd_3777297 < baseStart_3777297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777314 : List Nat := [3, 3, 1, 1, 2, 2, 2, 1, 2, 6]
def baseStart_3777314 : Nat := 118140960795 + 3777314 * 2 ^ 59
def prefixEnd_3777314 : Nat := 4983230072969 + 3 ^ 40 * 3777314 * 2
def baseEnd_3777314 : Nat := 646525888319113158434485

theorem tailTrace_3777314 : CollatzResearch.WordTrace tailWord_3777314 prefixEnd_3777314 646525888319113158434485 := by
  unfold tailWord_3777314
  simp only [CollatzResearch.WordTrace]
  refine ⟨34442489959360991679042749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91846639891629311144113997 34442489959360991679042749)
  ·
    refine ⟨12915933734760371879641031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34442489959360991679042749 12915933734760371879641031)
    ·
      refine ⟨19373900602140557819461547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12915933734760371879641031 19373900602140557819461547)
      ·
        refine ⟨29060850903210836729192321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19373900602140557819461547 29060850903210836729192321)
        ·
          refine ⟨21795638177408127546894241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29060850903210836729192321 21795638177408127546894241)
          ·
            refine ⟨16346728633056095660170681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21795638177408127546894241 16346728633056095660170681)
            ·
              refine ⟨12260046474792071745128011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16346728633056095660170681 12260046474792071745128011)
              ·
                refine ⟨18390069712188107617692017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12260046474792071745128011 18390069712188107617692017)
                ·
                  refine ⟨13792552284141080713269013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18390069712188107617692017 13792552284141080713269013)
                  ·
                    refine ⟨646525888319113158434485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13792552284141080713269013 646525888319113158434485)
                    ·
                      rfl

theorem cell23_3777314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_3777314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777314 prefixEnd_3777314 := by exact prefixLift 3777314
  have htrace : WordTrace (prefixWord ++ tailWord_3777314) baseStart_3777314 baseEnd_3777314 := by
    simpa [prefixWord, tailWord_3777314, baseEnd_3777314] using wordTrace_append hprefix tailTrace_3777314
  have hstable : (prefixWord ++ tailWord_3777314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777314).length < 2 ^ (prefixWord ++ tailWord_3777314).sum := by decide
  have hdescent : baseEnd_3777314 < baseStart_3777314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777341 : List Nat := [1, 4, 1, 4, 2, 1, 1, 1, 2, 1, 5]
def baseStart_3777341 : Nat := 118140960795 + 3777341 * 2 ^ 59
def prefixEnd_3777341 : Nat := 4983230072969 + 3 ^ 40 * 3777341 * 2
def baseEnd_3777341 : Nat := 1939591528935010869665831

theorem tailTrace_3777341 : CollatzResearch.WordTrace tailWord_3777341 prefixEnd_3777341 1939591528935010869665831 := by
  unfold tailWord_3777341
  simp only [CollatzResearch.WordTrace]
  refine ⟨137770944608346150327403877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91847296405564100218269251 137770944608346150327403877)
  ·
    refine ⟨25832052114064903186388227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137770944608346150327403877 25832052114064903186388227)
    ·
      refine ⟨38748078171097354779582341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25832052114064903186388227 38748078171097354779582341)
      ·
        refine ⟨7265264657080754021171689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38748078171097354779582341 7265264657080754021171689)
        ·
          refine ⟨5448948492810565515878767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7265264657080754021171689 5448948492810565515878767)
          ·
            refine ⟨8173422739215848273818151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5448948492810565515878767 8173422739215848273818151)
            ·
              refine ⟨12260134108823772410727227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8173422739215848273818151 12260134108823772410727227)
              ·
                refine ⟨18390201163235658616090841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12260134108823772410727227 18390201163235658616090841)
                ·
                  refine ⟨13792650872426743962068131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18390201163235658616090841 13792650872426743962068131)
                  ·
                    refine ⟨20688976308640115943102197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13792650872426743962068131 20688976308640115943102197)
                    ·
                      refine ⟨1939591528935010869665831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20688976308640115943102197 1939591528935010869665831)
                      ·
                        rfl

theorem cell23_3777341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_3777341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777341 prefixEnd_3777341 := by exact prefixLift 3777341
  have htrace : WordTrace (prefixWord ++ tailWord_3777341) baseStart_3777341 baseEnd_3777341 := by
    simpa [prefixWord, tailWord_3777341, baseEnd_3777341] using wordTrace_append hprefix tailTrace_3777341
  have hstable : (prefixWord ++ tailWord_3777341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777341).length < 2 ^ (prefixWord ++ tailWord_3777341).sum := by decide
  have hdescent : baseEnd_3777341 < baseStart_3777341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777354 : List Nat := [3, 1, 2, 1, 1, 1, 2, 4, 2, 3, 3]
def baseStart_3777354 : Nat := 118140960795 + 3777354 * 2 ^ 59
def prefixEnd_3777354 : Nat := 4983230072969 + 3 ^ 40 * 3777354 * 2
def baseEnd_3777354 : Nat := 1939598204183519318803271

theorem tailTrace_3777354 : CollatzResearch.WordTrace tailWord_3777354 prefixEnd_3777354 1939598204183519318803271 := by
  unfold tailWord_3777354
  simp only [CollatzResearch.WordTrace]
  refine ⟨34442854689324763386906779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91847612504866035698418077 34442854689324763386906779)
  ·
    refine ⟨51664282033987145080360169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34442854689324763386906779 51664282033987145080360169)
    ·
      refine ⟨38748211525490358810270127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51664282033987145080360169 38748211525490358810270127)
      ·
        refine ⟨58122317288235538215405191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38748211525490358810270127 58122317288235538215405191)
        ·
          refine ⟨87183475932353307323107787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58122317288235538215405191 87183475932353307323107787)
          ·
            refine ⟨130775213898529960984661681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87183475932353307323107787 130775213898529960984661681)
            ·
              refine ⟨98081410423897470738496261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130775213898529960984661681 98081410423897470738496261)
              ·
                refine ⟨18390264454480775763468049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98081410423897470738496261 18390264454480775763468049)
                ·
                  refine ⟨13792698340860581822601037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18390264454480775763468049 13792698340860581822601037)
                  ·
                    refine ⟨5172261877822718183475389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13792698340860581822601037 5172261877822718183475389)
                    ·
                      refine ⟨1939598204183519318803271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5172261877822718183475389 1939598204183519318803271)
                      ·
                        rfl

theorem cell23_3777354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_3777354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777354 prefixEnd_3777354 := by exact prefixLift 3777354
  have htrace : WordTrace (prefixWord ++ tailWord_3777354) baseStart_3777354 baseEnd_3777354 := by
    simpa [prefixWord, tailWord_3777354, baseEnd_3777354] using wordTrace_append hprefix tailTrace_3777354
  have hstable : (prefixWord ++ tailWord_3777354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777354).length < 2 ^ (prefixWord ++ tailWord_3777354).sum := by decide
  have hdescent : baseEnd_3777354 < baseStart_3777354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777361 : List Nat := [1, 2, 2, 1, 6, 2, 1, 1, 7]
def baseStart_3777361 : Nat := 118140960795 + 3777361 * 2 ^ 59
def prefixEnd_3777361 : Nat := 4983230072969 + 3 ^ 40 * 3777361 * 2
def baseEnd_3777361 : Nat := 215511310949788976823971

theorem tailTrace_3777361 : CollatzResearch.WordTrace tailWord_3777361 prefixEnd_3777361 215511310949788976823971 := by
  unfold tailWord_3777361
  simp only [CollatzResearch.WordTrace]
  refine ⟨137771674068273693743131937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91847782712182462495421291 137771674068273693743131937)
  ·
    refine ⟨103328755551205270307348953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137771674068273693743131937 103328755551205270307348953)
    ·
      refine ⟨77496566663403952730511715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103328755551205270307348953 77496566663403952730511715)
      ·
        refine ⟨116244849995105929095767573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77496566663403952730511715 116244849995105929095767573)
        ·
          refine ⟨5448977343520590426364105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 116244849995105929095767573 5448977343520590426364105)
          ·
            refine ⟨4086733007640442819773079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5448977343520590426364105 4086733007640442819773079)
            ·
              refine ⟨6130099511460664229659619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4086733007640442819773079 6130099511460664229659619)
              ·
                refine ⟨9195149267190996344489429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6130099511460664229659619 9195149267190996344489429)
                ·
                  refine ⟨215511310949788976823971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9195149267190996344489429 215511310949788976823971)
                  ·
                    rfl

theorem cell23_3777361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 7].length) (baseStart_3777361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777361 prefixEnd_3777361 := by exact prefixLift 3777361
  have htrace : WordTrace (prefixWord ++ tailWord_3777361) baseStart_3777361 baseEnd_3777361 := by
    simpa [prefixWord, tailWord_3777361, baseEnd_3777361] using wordTrace_append hprefix tailTrace_3777361
  have hstable : (prefixWord ++ tailWord_3777361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777361).length < 2 ^ (prefixWord ++ tailWord_3777361).sum := by decide
  have hdescent : baseEnd_3777361 < baseStart_3777361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777372 : List Nat := [2, 2, 4, 2, 1, 1, 4, 1, 2, 2, 2]
def baseStart_3777372 : Nat := 118140960795 + 3777372 * 2 ^ 59
def prefixEnd_3777372 : Nat := 4983230072969 + 3 ^ 40 * 3777372 * 2
def baseEnd_3777372 : Nat := 1939607446835300248378189

theorem tailTrace_3777372 : CollatzResearch.WordTrace tailWord_3777372 prefixEnd_3777372 1939607446835300248378189 := by
  unfold tailWord_3777372
  simp only [CollatzResearch.WordTrace]
  refine ⟨68886037635616921310891185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91848050180822561747854913 68886037635616921310891185)
  ·
    refine ⟨51664528226712690983168389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68886037635616921310891185 51664528226712690983168389)
    ·
      refine ⟨9687099042508629559344073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51664528226712690983168389 9687099042508629559344073)
      ·
        refine ⟨7265324281881472169508055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9687099042508629559344073 7265324281881472169508055)
        ·
          refine ⟨10897986422822208254262083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7265324281881472169508055 10897986422822208254262083)
          ·
            refine ⟨16346979634233312381393125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10897986422822208254262083 16346979634233312381393125)
            ·
              refine ⟨3065058681418746071511211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16346979634233312381393125 3065058681418746071511211)
              ·
                refine ⟨4597588022128119107266817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3065058681418746071511211 4597588022128119107266817)
                ·
                  refine ⟨3448191016596089330450113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4597588022128119107266817 3448191016596089330450113)
                  ·
                    refine ⟨2586143262447066997837585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3448191016596089330450113 2586143262447066997837585)
                    ·
                      refine ⟨1939607446835300248378189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2586143262447066997837585 1939607446835300248378189)
                      ·
                        rfl

theorem cell23_3777372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_3777372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777372 prefixEnd_3777372 := by exact prefixLift 3777372
  have htrace : WordTrace (prefixWord ++ tailWord_3777372) baseStart_3777372 baseEnd_3777372 := by
    simpa [prefixWord, tailWord_3777372, baseEnd_3777372] using wordTrace_append hprefix tailTrace_3777372
  have hstable : (prefixWord ++ tailWord_3777372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777372).length < 2 ^ (prefixWord ++ tailWord_3777372).sum := by decide
  have hdescent : baseEnd_3777372 < baseStart_3777372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777387 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 2, 8]
def baseStart_3777387 : Nat := 118140960795 + 3777387 * 2 ^ 59
def prefixEnd_3777387 : Nat := 4983230072969 + 3 ^ 40 * 3777387 * 2
def baseEnd_3777387 : Nat := 646538383015039229896873

theorem tailTrace_3777387 : CollatzResearch.WordTrace tailWord_3777387 prefixEnd_3777387 646538383015039229896873 := by
  unfold tailWord_3777387
  simp only [CollatzResearch.WordTrace]
  refine ⟨137772622366179500183578415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91848414910786333455718943 137772622366179500183578415)
  ·
    refine ⟨206658933549269250275367623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137772622366179500183578415 206658933549269250275367623)
    ·
      refine ⟨309988400323903875413051435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206658933549269250275367623 309988400323903875413051435)
      ·
        refine ⟨464982600485855813119577153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309988400323903875413051435 464982600485855813119577153)
        ·
          refine ⟨348736950364391859839682865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464982600485855813119577153 348736950364391859839682865)
          ·
            refine ⟨261552712773293894879762149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348736950364391859839682865 261552712773293894879762149)
            ·
              refine ⟨49041133644992605289955403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 261552712773293894879762149 49041133644992605289955403)
              ·
                refine ⟨73561700467488907934933105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49041133644992605289955403 73561700467488907934933105)
                ·
                  refine ⟨55171275350616680951199829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73561700467488907934933105 55171275350616680951199829)
                  ·
                    refine ⟨646538383015039229896873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55171275350616680951199829 646538383015039229896873)
                    ·
                      rfl

theorem cell23_3777387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 8].length) (baseStart_3777387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777387 prefixEnd_3777387 := by exact prefixLift 3777387
  have htrace : WordTrace (prefixWord ++ tailWord_3777387) baseStart_3777387 baseEnd_3777387 := by
    simpa [prefixWord, tailWord_3777387, baseEnd_3777387] using wordTrace_append hprefix tailTrace_3777387
  have hstable : (prefixWord ++ tailWord_3777387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777387).length < 2 ^ (prefixWord ++ tailWord_3777387).sum := by decide
  have hdescent : baseEnd_3777387 < baseStart_3777387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777394 : List Nat := [3, 2, 1, 2, 1, 1, 2, 3, 1, 3, 4]
def baseStart_3777394 : Nat := 118140960795 + 3777394 * 2 ^ 59
def prefixEnd_3777394 : Nat := 4983230072969 + 3 ^ 40 * 3777394 * 2
def baseEnd_3777394 : Nat := 1939618743409699162303087

theorem tailTrace_3777394 : CollatzResearch.WordTrace tailWord_3777394 prefixEnd_3777394 1939618743409699162303087 := by
  unfold tailWord_3777394
  simp only [CollatzResearch.WordTrace]
  refine ⟨34443219419288535094770809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91848585118102760252722157 34443219419288535094770809)
  ·
    refine ⟨25832414564466401321078107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34443219419288535094770809 25832414564466401321078107)
    ·
      refine ⟨38748621846699601981617161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25832414564466401321078107 38748621846699601981617161)
      ·
        refine ⟨29061466385024701486212871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38748621846699601981617161 29061466385024701486212871)
        ·
          refine ⟨43592199577537052229319307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29061466385024701486212871 43592199577537052229319307)
          ·
            refine ⟨65388299366305578343978961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43592199577537052229319307 65388299366305578343978961)
            ·
              refine ⟨49041224524729183757984221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65388299366305578343978961 49041224524729183757984221)
              ·
                refine ⟨18390459196773443909244083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49041224524729183757984221 18390459196773443909244083)
                ·
                  refine ⟨27585688795160165863866125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18390459196773443909244083 27585688795160165863866125)
                  ·
                    refine ⟨10344633298185062198949797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27585688795160165863866125 10344633298185062198949797)
                    ·
                      refine ⟨1939618743409699162303087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10344633298185062198949797 1939618743409699162303087)
                      ·
                        rfl

theorem cell23_3777394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_3777394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777394 prefixEnd_3777394 := by exact prefixLift 3777394
  have htrace : WordTrace (prefixWord ++ tailWord_3777394) baseStart_3777394 baseEnd_3777394 := by
    simpa [prefixWord, tailWord_3777394, baseEnd_3777394] using wordTrace_append hprefix tailTrace_3777394
  have hstable : (prefixWord ++ tailWord_3777394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777394).length < 2 ^ (prefixWord ++ tailWord_3777394).sum := by decide
  have hdescent : baseEnd_3777394 < baseStart_3777394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777411 : List Nat := [1, 1, 1, 3, 4, 1, 2, 2, 2, 4, 2]
def baseStart_3777411 : Nat := 118140960795 + 3777411 * 2 ^ 59
def prefixEnd_3777411 : Nat := 4983230072969 + 3 ^ 40 * 3777411 * 2
def baseEnd_3777411 : Nat := 1939627472580825595790509

theorem tailTrace_3777411 : CollatzResearch.WordTrace tailWord_3777411 prefixEnd_3777411 1939627472580825595790509 := by
  unfold tailWord_3777411
  simp only [CollatzResearch.WordTrace]
  refine ⟨137773497718092552282452087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91848998478728368188301391 137773497718092552282452087)
  ·
    refine ⟨206660246577138828423678131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137773497718092552282452087 206660246577138828423678131)
    ·
      refine ⟨309990369865708242635517197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206660246577138828423678131 309990369865708242635517197)
      ·
        refine ⟨116246388699640590988318949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309990369865708242635517197 116246388699640590988318949)
        ·
          refine ⟨21796197881182610810309803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116246388699640590988318949 21796197881182610810309803)
          ·
            refine ⟨32694296821773916215464705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21796197881182610810309803 32694296821773916215464705)
            ·
              refine ⟨24520722616330437161598529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32694296821773916215464705 24520722616330437161598529)
              ·
                refine ⟨18390541962247827871198897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24520722616330437161598529 18390541962247827871198897)
                ·
                  refine ⟨13792906471685870903399173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18390541962247827871198897 13792906471685870903399173)
                  ·
                    refine ⟨2586169963441100794387345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13792906471685870903399173 2586169963441100794387345)
                    ·
                      refine ⟨1939627472580825595790509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2586169963441100794387345 1939627472580825595790509)
                      ·
                        rfl

theorem cell23_3777411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 4, 2].length) (baseStart_3777411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777411 prefixEnd_3777411 := by exact prefixLift 3777411
  have htrace : WordTrace (prefixWord ++ tailWord_3777411) baseStart_3777411 baseEnd_3777411 := by
    simpa [prefixWord, tailWord_3777411, baseEnd_3777411] using wordTrace_append hprefix tailTrace_3777411
  have hstable : (prefixWord ++ tailWord_3777411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777411).length < 2 ^ (prefixWord ++ tailWord_3777411).sum := by decide
  have hdescent : baseEnd_3777411 < baseStart_3777411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777428 : List Nat := [2, 4, 2, 1, 1, 1, 3, 1, 2, 4, 2]
def baseStart_3777428 : Nat := 118140960795 + 3777428 * 2 ^ 59
def prefixEnd_3777428 : Nat := 4983230072969 + 3 ^ 40 * 3777428 * 2
def baseEnd_3777428 : Nat := 1939636201751952029277931

theorem tailTrace_3777428 : CollatzResearch.WordTrace tailWord_3777428 prefixEnd_3777428 1939636201751952029277931 := by
  unfold tailWord_3777428
  simp only [CollatzResearch.WordTrace]
  refine ⟨68887058879515482092910469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91849411839353976123880625 68887058879515482092910469)
  ·
    refine ⟨12916323539909152892420713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68887058879515482092910469 12916323539909152892420713)
    ·
      refine ⟨9687242654931864669315535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12916323539909152892420713 9687242654931864669315535)
      ·
        refine ⟨14530863982397797003973303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9687242654931864669315535 14530863982397797003973303)
        ·
          refine ⟨21796295973596695505959955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14530863982397797003973303 21796295973596695505959955)
          ·
            refine ⟨32694443960395043258939933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21796295973596695505959955 32694443960395043258939933)
            ·
              refine ⟨12260416485148141222102475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32694443960395043258939933 12260416485148141222102475)
              ·
                refine ⟨18390624727722211833153713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12260416485148141222102475 18390624727722211833153713)
                ·
                  refine ⟨13792968545791658874865285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18390624727722211833153713 13792968545791658874865285)
                  ·
                    refine ⟨2586181602335936039037241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13792968545791658874865285 2586181602335936039037241)
                    ·
                      refine ⟨1939636201751952029277931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2586181602335936039037241 1939636201751952029277931)
                      ·
                        rfl

theorem cell23_3777428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_3777428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777428 prefixEnd_3777428 := by exact prefixLift 3777428
  have htrace : WordTrace (prefixWord ++ tailWord_3777428) baseStart_3777428 baseEnd_3777428 := by
    simpa [prefixWord, tailWord_3777428, baseEnd_3777428] using wordTrace_append hprefix tailTrace_3777428
  have hstable : (prefixWord ++ tailWord_3777428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777428).length < 2 ^ (prefixWord ++ tailWord_3777428).sum := by decide
  have hdescent : baseEnd_3777428 < baseStart_3777428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777498 : List Nat := [3, 1, 1, 2, 4, 2, 2, 2, 1, 5]
def baseStart_3777498 : Nat := 118140960795 + 3777498 * 2 ^ 59
def prefixEnd_3777498 : Nat := 4983230072969 + 3 ^ 40 * 3777498 * 2
def baseEnd_3777498 : Nat := 646557381799255585134203

theorem tailTrace_3777498 : CollatzResearch.WordTrace tailWord_3777498 prefixEnd_3777498 646557381799255585134203 := by
  unfold tailWord_3777498
  simp only [CollatzResearch.WordTrace]
  refine ⟨34444167717194341535217287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91851113912518244093912765 34444167717194341535217287)
  ·
    refine ⟨51666251575791512302825931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34444167717194341535217287 51666251575791512302825931)
    ·
      refine ⟨77499377363687268454238897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51666251575791512302825931 77499377363687268454238897)
      ·
        refine ⟨58124533022765451340679173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77499377363687268454238897 58124533022765451340679173)
        ·
          refine ⟨10898349941768522126377345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58124533022765451340679173 10898349941768522126377345)
          ·
            refine ⟨8173762456326391594783009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10898349941768522126377345 8173762456326391594783009)
            ·
              refine ⟨6130321842244793696087257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8173762456326391594783009 6130321842244793696087257)
              ·
                refine ⟨4597741381683595272065443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6130321842244793696087257 4597741381683595272065443)
                ·
                  refine ⟨6896612072525392908098165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4597741381683595272065443 6896612072525392908098165)
                  ·
                    refine ⟨646557381799255585134203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6896612072525392908098165 646557381799255585134203)
                    ·
                      rfl

theorem cell23_3777498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 1, 5].length) (baseStart_3777498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777498 prefixEnd_3777498 := by exact prefixLift 3777498
  have htrace : WordTrace (prefixWord ++ tailWord_3777498) baseStart_3777498 baseEnd_3777498 := by
    simpa [prefixWord, tailWord_3777498, baseEnd_3777498] using wordTrace_append hprefix tailTrace_3777498
  have hstable : (prefixWord ++ tailWord_3777498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777498).length < 2 ^ (prefixWord ++ tailWord_3777498).sum := by decide
  have hdescent : baseEnd_3777498 < baseStart_3777498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777521 : List Nat := [1, 2, 2, 2, 4, 1, 1, 3, 1, 1, 5]
def baseStart_3777521 : Nat := 118140960795 + 3777521 * 2 ^ 59
def prefixEnd_3777521 : Nat := 4983230072969 + 3 ^ 40 * 3777521 * 2
def baseEnd_3777521 : Nat := 1939683955452820165415003

theorem tailTrace_3777521 : CollatzResearch.WordTrace tailWord_3777521 prefixEnd_3777521 1939683955452820165415003 := by
  unfold tailWord_3777521
  simp only [CollatzResearch.WordTrace]
  refine ⟨137777509747694041068956417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91851673165129360712637611 137777509747694041068956417)
  ·
    refine ⟨103333132310770530801717313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137777509747694041068956417 103333132310770530801717313)
    ·
      refine ⟨77499849233077898101287985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103333132310770530801717313 77499849233077898101287985)
      ·
        refine ⟨58124886924808423575965989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77499849233077898101287985 58124886924808423575965989)
        ·
          refine ⟨10898416298401579420493623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58124886924808423575965989 10898416298401579420493623)
          ·
            refine ⟨16347624447602369130740435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10898416298401579420493623 16347624447602369130740435)
            ·
              refine ⟨24521436671403553696110653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16347624447602369130740435 24521436671403553696110653)
              ·
                refine ⟨9195538751776332636041495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24521436671403553696110653 9195538751776332636041495)
                ·
                  refine ⟨13793308127664498954062243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9195538751776332636041495 13793308127664498954062243)
                  ·
                    refine ⟨20689962191496748431093365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13793308127664498954062243 20689962191496748431093365)
                    ·
                      refine ⟨1939683955452820165415003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20689962191496748431093365 1939683955452820165415003)
                      ·
                        rfl

theorem cell23_3777521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_3777521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777521 prefixEnd_3777521 := by exact prefixLift 3777521
  have htrace : WordTrace (prefixWord ++ tailWord_3777521) baseStart_3777521 baseEnd_3777521 := by
    simpa [prefixWord, tailWord_3777521, baseEnd_3777521] using wordTrace_append hprefix tailTrace_3777521
  have hstable : (prefixWord ++ tailWord_3777521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777521).length < 2 ^ (prefixWord ++ tailWord_3777521).sum := by decide
  have hdescent : baseEnd_3777521 < baseStart_3777521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777522 : List Nat := [3, 2, 1, 5, 1, 1, 1, 2, 2, 3, 2]
def baseStart_3777522 : Nat := 118140960795 + 3777522 * 2 ^ 59
def prefixEnd_3777522 : Nat := 4983230072969 + 3 ^ 40 * 3777522 * 2
def baseEnd_3777522 : Nat := 1939684468933474661502499

theorem tailTrace_3777522 : CollatzResearch.WordTrace tailWord_3777522 prefixEnd_3777522 1939684468933474661502499 := by
  unfold tailWord_3777522
  simp only [CollatzResearch.WordTrace]
  refine ⟨34444386555172604559935705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91851697480460278826495213 34444386555172604559935705)
  ·
    refine ⟨25833289916379453419951779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34444386555172604559935705 25833289916379453419951779)
    ·
      refine ⟨38749934874569180129927669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25833289916379453419951779 38749934874569180129927669)
      ·
        refine ⟨3632806394490860637180719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38749934874569180129927669 3632806394490860637180719)
        ·
          refine ⟨5449209591736290955771079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3632806394490860637180719 5449209591736290955771079)
          ·
            refine ⟨8173814387604436433656619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5449209591736290955771079 8173814387604436433656619)
            ·
              refine ⟨12260721581406654650484929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8173814387604436433656619 12260721581406654650484929)
              ·
                refine ⟨9195541186054990987863697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12260721581406654650484929 9195541186054990987863697)
                ·
                  refine ⟨6896655889541243240897773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9195541186054990987863697 6896655889541243240897773)
                  ·
                    refine ⟨2586245958577966215336665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6896655889541243240897773 2586245958577966215336665)
                    ·
                      refine ⟨1939684468933474661502499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2586245958577966215336665 1939684468933474661502499)
                      ·
                        rfl

theorem cell23_3777522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_3777522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777522 prefixEnd_3777522 := by exact prefixLift 3777522
  have htrace : WordTrace (prefixWord ++ tailWord_3777522) baseStart_3777522 baseEnd_3777522 := by
    simpa [prefixWord, tailWord_3777522, baseEnd_3777522] using wordTrace_append hprefix tailTrace_3777522
  have hstable : (prefixWord ++ tailWord_3777522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777522).length < 2 ^ (prefixWord ++ tailWord_3777522).sum := by decide
  have hdescent : baseEnd_3777522 < baseStart_3777522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777572 : List Nat := [2, 3, 1, 4, 1, 2, 3, 1, 1, 2, 3]
def baseStart_3777572 : Nat := 118140960795 + 3777572 * 2 ^ 59
def prefixEnd_3777572 : Nat := 4983230072969 + 3 ^ 40 * 3777572 * 2
def baseEnd_3777572 : Nat := 1939710142966199465877269

theorem tailTrace_3777572 : CollatzResearch.WordTrace tailWord_3777572 prefixEnd_3777572 1939710142966199465877269 := by
  unfold tailWord_3777572
  simp only [CollatzResearch.WordTrace]
  refine ⟨68889684935254638389531485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91852913247006184519375313 68889684935254638389531485)
  ·
    refine ⟨25833631850720489396074307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68889684935254638389531485 25833631850720489396074307)
    ·
      refine ⟨38750447776080734094111461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25833631850720489396074307 38750447776080734094111461)
      ·
        refine ⟨7265708958015137642645899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38750447776080734094111461 7265708958015137642645899)
        ·
          refine ⟨10898563437022706463968849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7265708958015137642645899 10898563437022706463968849)
          ·
            refine ⟨8173922577767029847976637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10898563437022706463968849 8173922577767029847976637)
            ·
              refine ⟨3065220966662636192991239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8173922577767029847976637 3065220966662636192991239)
              ·
                refine ⟨4597831449993954289486859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3065220966662636192991239 4597831449993954289486859)
                ·
                  refine ⟨6896747174990931434230289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4597831449993954289486859 6896747174990931434230289)
                  ·
                    refine ⟨5172560381243198575672717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6896747174990931434230289 5172560381243198575672717)
                    ·
                      refine ⟨1939710142966199465877269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5172560381243198575672717 1939710142966199465877269)
                      ·
                        rfl

theorem cell23_3777572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_3777572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777572 prefixEnd_3777572 := by exact prefixLift 3777572
  have htrace : WordTrace (prefixWord ++ tailWord_3777572) baseStart_3777572 baseEnd_3777572 := by
    simpa [prefixWord, tailWord_3777572, baseEnd_3777572] using wordTrace_append hprefix tailTrace_3777572
  have hstable : (prefixWord ++ tailWord_3777572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777572).length < 2 ^ (prefixWord ++ tailWord_3777572).sum := by decide
  have hdescent : baseEnd_3777572 < baseStart_3777572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777585 : List Nat := [1, 2, 2, 3, 1, 2, 4, 2, 2, 1, 3]
def baseStart_3777585 : Nat := 118140960795 + 3777585 * 2 ^ 59
def prefixEnd_3777585 : Nat := 4983230072969 + 3 ^ 40 * 3777585 * 2
def baseEnd_3777585 : Nat := 1939716818214707915014709

theorem tailTrace_3777585 : CollatzResearch.WordTrace tailWord_3777585 prefixEnd_3777585 1939716818214707915014709 := by
  unfold tailWord_3777585
  simp only [CollatzResearch.WordTrace]
  refine ⟨137779844019462179999286209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91853229346308119999524139 137779844019462179999286209)
  ·
    refine ⟨103334883014596634999464657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137779844019462179999286209 103334883014596634999464657)
    ·
      refine ⟨77501162260947476249598493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103334883014596634999464657 77501162260947476249598493)
      ·
        refine ⟨29062935847855303593599435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77501162260947476249598493 29062935847855303593599435)
        ·
          refine ⟨43594403771782955390399153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29062935847855303593599435 43594403771782955390399153)
          ·
            refine ⟨32695802828837216542799365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43594403771782955390399153 32695802828837216542799365)
            ·
              refine ⟨6130463030406978101774881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32695802828837216542799365 6130463030406978101774881)
              ·
                refine ⟨4597847272805233576331161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6130463030406978101774881 4597847272805233576331161)
                ·
                  refine ⟨3448385454603925182248371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4597847272805233576331161 3448385454603925182248371)
                  ·
                    refine ⟨5172578181905887773372557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3448385454603925182248371 5172578181905887773372557)
                    ·
                      refine ⟨1939716818214707915014709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5172578181905887773372557 1939716818214707915014709)
                      ·
                        rfl

theorem cell23_3777585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_3777585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777585 prefixEnd_3777585 := by exact prefixLift 3777585
  have htrace : WordTrace (prefixWord ++ tailWord_3777585) baseStart_3777585 baseEnd_3777585 := by
    simpa [prefixWord, tailWord_3777585, baseEnd_3777585] using wordTrace_append hprefix tailTrace_3777585
  have hstable : (prefixWord ++ tailWord_3777585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777585).length < 2 ^ (prefixWord ++ tailWord_3777585).sum := by decide
  have hdescent : baseEnd_3777585 < baseStart_3777585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777588 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 2, 7]
def baseStart_3777588 : Nat := 118140960795 + 3777588 * 2 ^ 59
def prefixEnd_3777588 : Nat := 4983230072969 + 3 ^ 40 * 3777588 * 2
def baseEnd_3777588 : Nat := 646572786218890467759065

theorem tailTrace_3777588 : CollatzResearch.WordTrace tailWord_3777588 prefixEnd_3777588 646572786218890467759065 := by
  unfold tailWord_3777588
  simp only [CollatzResearch.WordTrace]
  refine ⟨68889976719225655755822709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91853302292300874341096945 68889976719225655755822709)
  ·
    refine ⟨6458435317427405227108379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68889976719225655755822709 6458435317427405227108379)
    ·
      refine ⟨9687652976141107840662569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6458435317427405227108379 9687652976141107840662569)
      ·
        refine ⟨7265739732105830880496927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9687652976141107840662569 7265739732105830880496927)
        ·
          refine ⟨10898609598158746320745391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7265739732105830880496927 10898609598158746320745391)
          ·
            refine ⟨16347914397238119481118087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10898609598158746320745391 16347914397238119481118087)
            ·
              refine ⟨24521871595857179221677131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16347914397238119481118087 24521871595857179221677131)
              ·
                refine ⟨36782807393785768832515697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24521871595857179221677131 36782807393785768832515697)
                ·
                  refine ⟨27587105545339326624386773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36782807393785768832515697 27587105545339326624386773)
                  ·
                    refine ⟨646572786218890467759065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27587105545339326624386773 646572786218890467759065)
                    ·
                      rfl

theorem cell23_3777588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_3777588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777588 prefixEnd_3777588 := by exact prefixLift 3777588
  have htrace : WordTrace (prefixWord ++ tailWord_3777588) baseStart_3777588 baseEnd_3777588 := by
    simpa [prefixWord, tailWord_3777588, baseEnd_3777588] using wordTrace_append hprefix tailTrace_3777588
  have hstable : (prefixWord ++ tailWord_3777588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777588).length < 2 ^ (prefixWord ++ tailWord_3777588).sum := by decide
  have hdescent : baseEnd_3777588 < baseStart_3777588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777621 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 1, 4, 4]
def baseStart_3777621 : Nat := 118140960795 + 3777621 * 2 ^ 59
def prefixEnd_3777621 : Nat := 4983230072969 + 3 ^ 40 * 3777621 * 2
def baseEnd_3777621 : Nat := 1939735303518269774164543

theorem tailTrace_3777621 : CollatzResearch.WordTrace tailWord_3777621 prefixEnd_3777621 1939735303518269774164543 := by
  unfold tailWord_3777621
  simp only [CollatzResearch.WordTrace]
  refine ⟨137781157047331758147596717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91854104698221172098397811 137781157047331758147596717)
  ·
    refine ⟨51667933892749409305348769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137781157047331758147596717 51667933892749409305348769)
    ·
      refine ⟨38750950419562056979011577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51667933892749409305348769 38750950419562056979011577)
      ·
        refine ⟨29063212814671542734258683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38750950419562056979011577 29063212814671542734258683)
        ·
          refine ⟨43594819222007314101388025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29063212814671542734258683 43594819222007314101388025)
          ·
            refine ⟨32696114416505485576041019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43594819222007314101388025 32696114416505485576041019)
            ·
              refine ⟨49044171624758228364061529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32696114416505485576041019 49044171624758228364061529)
              ·
                refine ⟨36783128718568671273046147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49044171624758228364061529 36783128718568671273046147)
                ·
                  refine ⟨55174693077853006909569221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36783128718568671273046147 55174693077853006909569221)
                  ·
                    refine ⟨10345254952097438795544229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55174693077853006909569221 10345254952097438795544229)
                    ·
                      refine ⟨1939735303518269774164543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10345254952097438795544229 1939735303518269774164543)
                      ·
                        rfl

theorem cell23_3777621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_3777621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777621 prefixEnd_3777621 := by exact prefixLift 3777621
  have htrace : WordTrace (prefixWord ++ tailWord_3777621) baseStart_3777621 baseEnd_3777621 := by
    simpa [prefixWord, tailWord_3777621, baseEnd_3777621] using wordTrace_append hprefix tailTrace_3777621
  have hstable : (prefixWord ++ tailWord_3777621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777621).length < 2 ^ (prefixWord ++ tailWord_3777621).sum := by decide
  have hdescent : baseEnd_3777621 < baseStart_3777621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777629 : List Nat := [1, 4, 4, 1, 2, 1, 1, 3, 1, 3, 2]
def baseStart_3777629 : Nat := 118140960795 + 3777629 * 2 ^ 59
def prefixEnd_3777629 : Nat := 4983230072969 + 3 ^ 40 * 3777629 * 2
def baseEnd_3777629 : Nat := 1939739411363505742864507

theorem tailTrace_3777629 : CollatzResearch.WordTrace tailWord_3777629 prefixEnd_3777629 1939739411363505742864507 := by
  unfold tailWord_3777629
  simp only [CollatzResearch.WordTrace]
  refine ⟨137781448831302775513887941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91854299220868517009258627 137781448831302775513887941)
  ·
    refine ⟨25834021655869270408853989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137781448831302775513887941 25834021655869270408853989)
    ·
      refine ⟨4843879060475488201660123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25834021655869270408853989 4843879060475488201660123)
      ·
        refine ⟨7265818590713232302490185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4843879060475488201660123 7265818590713232302490185)
        ·
          refine ⟨5449363943034924226867639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7265818590713232302490185 5449363943034924226867639)
          ·
            refine ⟨8174045914552386340301459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5449363943034924226867639 8174045914552386340301459)
            ·
              refine ⟨12261068871828579510452189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8174045914552386340301459 12261068871828579510452189)
              ·
                refine ⟨4597900826935717316419571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12261068871828579510452189 4597900826935717316419571)
                ·
                  refine ⟨6896851240403575974629357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4597900826935717316419571 6896851240403575974629357)
                  ·
                    refine ⟨2586319215151340990486009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6896851240403575974629357 2586319215151340990486009)
                    ·
                      refine ⟨1939739411363505742864507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2586319215151340990486009 1939739411363505742864507)
                      ·
                        rfl

theorem cell23_3777629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_3777629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777629 prefixEnd_3777629 := by exact prefixLift 3777629
  have htrace : WordTrace (prefixWord ++ tailWord_3777629) baseStart_3777629 baseEnd_3777629 := by
    simpa [prefixWord, tailWord_3777629, baseEnd_3777629] using wordTrace_append hprefix tailTrace_3777629
  have hstable : (prefixWord ++ tailWord_3777629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777629).length < 2 ^ (prefixWord ++ tailWord_3777629).sum := by decide
  have hdescent : baseEnd_3777629 < baseStart_3777629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777642 : List Nat := [3, 1, 3, 2, 2, 2, 1, 1, 4, 2, 2]
def baseStart_3777642 : Nat := 118140960795 + 3777642 * 2 ^ 59
def prefixEnd_3777642 : Nat := 4983230072969 + 3 ^ 40 * 3777642 * 2
def baseEnd_3777642 : Nat := 1939746086612014192001947

theorem tailTrace_3777642 : CollatzResearch.WordTrace tailWord_3777642 prefixEnd_3777642 1939746086612014192001947 := by
  unfold tailWord_3777642
  simp only [CollatzResearch.WordTrace]
  refine ⟨34445480745063919683527795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91854615320170452489407453 34445480745063919683527795)
  ·
    refine ⟨51668221117595879525291693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34445480745063919683527795 51668221117595879525291693)
    ·
      refine ⟨19375582919098454821984385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51668221117595879525291693 19375582919098454821984385)
      ·
        refine ⟨14531687189323841116488289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19375582919098454821984385 14531687189323841116488289)
        ·
          refine ⟨10898765391992880837366217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14531687189323841116488289 10898765391992880837366217)
          ·
            refine ⟨8174074043994660628024663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10898765391992880837366217 8174074043994660628024663)
            ·
              refine ⟨12261111065991990942036995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8174074043994660628024663 12261111065991990942036995)
              ·
                refine ⟨18391666598987986413055493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12261111065991990942036995 18391666598987986413055493)
                ·
                  refine ⟨3448437487310247452447905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18391666598987986413055493 3448437487310247452447905)
                  ·
                    refine ⟨2586328115482685589335929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3448437487310247452447905 2586328115482685589335929)
                    ·
                      refine ⟨1939746086612014192001947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2586328115482685589335929 1939746086612014192001947)
                      ·
                        rfl

theorem cell23_3777642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_3777642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777642 prefixEnd_3777642 := by exact prefixLift 3777642
  have htrace : WordTrace (prefixWord ++ tailWord_3777642) baseStart_3777642 baseEnd_3777642 := by
    simpa [prefixWord, tailWord_3777642, baseEnd_3777642] using wordTrace_append hprefix tailTrace_3777642
  have hstable : (prefixWord ++ tailWord_3777642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777642).length < 2 ^ (prefixWord ++ tailWord_3777642).sum := by decide
  have hdescent : baseEnd_3777642 < baseStart_3777642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777648 : List Nat := [2, 1, 1, 1, 5, 1, 1, 6, 5]
def baseStart_3777648 : Nat := 118140960795 + 3777648 * 2 ^ 59
def prefixEnd_3777648 : Nat := 4983230072969 + 3 ^ 40 * 3777648 * 2
def baseEnd_3777648 : Nat := 215527685277326796502991

theorem tailTrace_3777648 : CollatzResearch.WordTrace tailWord_3777648 prefixEnd_3777648 215527685277326796502991 := by
  unfold tailWord_3777648
  simp only [CollatzResearch.WordTrace]
  refine ⟨68891070909116970879414799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91854761212155961172553065 68891070909116970879414799)
  ·
    refine ⟨103336606363675456319122199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68891070909116970879414799 103336606363675456319122199)
    ·
      refine ⟨155004909545513184478683299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103336606363675456319122199 155004909545513184478683299)
      ·
        refine ⟨232507364318269776718024949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155004909545513184478683299 232507364318269776718024949)
        ·
          refine ⟨21797565404837791567314839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 232507364318269776718024949 21797565404837791567314839)
          ·
            refine ⟨32696348107256687350972259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21797565404837791567314839 32696348107256687350972259)
            ·
              refine ⟨49044522160885031026458389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32696348107256687350972259 49044522160885031026458389)
              ·
                refine ⟨2298961976291485829365237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49044522160885031026458389 2298961976291485829365237)
                ·
                  refine ⟨215527685277326796502991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2298961976291485829365237 215527685277326796502991)
                  ·
                    rfl

theorem cell23_3777648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 6, 5].length) (baseStart_3777648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777648 prefixEnd_3777648 := by exact prefixLift 3777648
  have htrace : WordTrace (prefixWord ++ tailWord_3777648) baseStart_3777648 baseEnd_3777648 := by
    simpa [prefixWord, tailWord_3777648, baseEnd_3777648] using wordTrace_append hprefix tailTrace_3777648
  have hstable : (prefixWord ++ tailWord_3777648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777648).length < 2 ^ (prefixWord ++ tailWord_3777648).sum := by decide
  have hdescent : baseEnd_3777648 < baseStart_3777648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777661 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 3, 7]
def baseStart_3777661 : Nat := 118140960795 + 3777661 * 2 ^ 59
def prefixEnd_3777661 : Nat := 4983230072969 + 3 ^ 40 * 3777661 * 2
def baseEnd_3777661 : Nat := 646585280914816539221453

theorem tailTrace_3777661 : CollatzResearch.WordTrace tailWord_3777661 prefixEnd_3777661 646585280914816539221453 := by
  unfold tailWord_3777661
  simp only [CollatzResearch.WordTrace]
  refine ⟨137782615967186844979052837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91855077311457896652701891 137782615967186844979052837)
  ·
    refine ⟨25834240493847533433572407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137782615967186844979052837 25834240493847533433572407)
    ·
      refine ⟨38751360740771300150358611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25834240493847533433572407 38751360740771300150358611)
      ·
        refine ⟨58127041111156950225537917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38751360740771300150358611 58127041111156950225537917)
        ·
          refine ⟨21797640416683856334576719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58127041111156950225537917 21797640416683856334576719)
          ·
            refine ⟨32696460625025784501865079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21797640416683856334576719 32696460625025784501865079)
            ·
              refine ⟨49044690937538676752797619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32696460625025784501865079 49044690937538676752797619)
              ·
                refine ⟨73567036406308015129196429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49044690937538676752797619 73567036406308015129196429)
                ·
                  refine ⟨27587638652365505673448661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73567036406308015129196429 27587638652365505673448661)
                  ·
                    refine ⟨646585280914816539221453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27587638652365505673448661 646585280914816539221453)
                    ·
                      rfl

theorem cell23_3777661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_3777661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777661 prefixEnd_3777661 := by exact prefixLift 3777661
  have htrace : WordTrace (prefixWord ++ tailWord_3777661) baseStart_3777661 baseEnd_3777661 := by
    simpa [prefixWord, tailWord_3777661, baseEnd_3777661] using wordTrace_append hprefix tailTrace_3777661
  have hstable : (prefixWord ++ tailWord_3777661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777661).length < 2 ^ (prefixWord ++ tailWord_3777661).sum := by decide
  have hdescent : baseEnd_3777661 < baseStart_3777661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777671 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 5]
def baseStart_3777671 : Nat := 118140960795 + 3777671 * 2 ^ 59
def prefixEnd_3777671 : Nat := 4983230072969 + 3 ^ 40 * 3777671 * 2
def baseEnd_3777671 : Nat := 1939760977550994578539313

theorem tailTrace_3777671 : CollatzResearch.WordTrace tailWord_3777671 prefixEnd_3777671 1939760977550994578539313 := by
  unfold tailWord_3777671
  simp only [CollatzResearch.WordTrace]
  refine ⟨137782980697150616686916867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91855320464767077791277911 137782980697150616686916867)
  ·
    refine ⟨206674471045725925030375301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137782980697150616686916867 206674471045725925030375301)
    ·
      refine ⟨38751463321073610943195369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206674471045725925030375301 38751463321073610943195369)
      ·
        refine ⟨29063597490805208207396527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38751463321073610943195369 29063597490805208207396527)
        ·
          refine ⟨43595396236207812311094791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29063597490805208207396527 43595396236207812311094791)
          ·
            refine ⟨65393094354311718466642187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43595396236207812311094791 65393094354311718466642187)
            ·
              refine ⟨98089641531467577699963281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65393094354311718466642187 98089641531467577699963281)
              ·
                refine ⟨73567231148600683274972461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98089641531467577699963281 73567231148600683274972461)
                ·
                  refine ⟨27587711680725256228114673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73567231148600683274972461 27587711680725256228114673)
                  ·
                    refine ⟨20690783760543942171086005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27587711680725256228114673 20690783760543942171086005)
                    ·
                      refine ⟨1939760977550994578539313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20690783760543942171086005 1939760977550994578539313)
                      ·
                        rfl

theorem cell23_3777671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_3777671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777671 prefixEnd_3777671 := by exact prefixLift 3777671
  have htrace : WordTrace (prefixWord ++ tailWord_3777671) baseStart_3777671 baseEnd_3777671 := by
    simpa [prefixWord, tailWord_3777671, baseEnd_3777671] using wordTrace_append hprefix tailTrace_3777671
  have hstable : (prefixWord ++ tailWord_3777671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777671).length < 2 ^ (prefixWord ++ tailWord_3777671).sum := by decide
  have hdescent : baseEnd_3777671 < baseStart_3777671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777678 : List Nat := [4, 1, 1, 3, 2, 1, 2, 1, 1, 7]
def baseStart_3777678 : Nat := 118140960795 + 3777678 * 2 ^ 59
def prefixEnd_3777678 : Nat := 4983230072969 + 3 ^ 40 * 3777678 * 2
def baseEnd_3777678 : Nat := 646588190638525350383927

theorem tailTrace_3777678 : CollatzResearch.WordTrace tailWord_3777678 prefixEnd_3777678 646588190638525350383927 := by
  unfold tailWord_3777678
  simp only [CollatzResearch.WordTrace]
  refine ⟨17222904501015657110302711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91855490672083504588281125 17222904501015657110302711)
  ·
    refine ⟨25834356751523485665454067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17222904501015657110302711 25834356751523485665454067)
    ·
      refine ⟨38751535127285228498181101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25834356751523485665454067 38751535127285228498181101)
      ·
        refine ⟨14531825672731960686817913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38751535127285228498181101 14531825672731960686817913)
        ·
          refine ⟨10898869254548970515113435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14531825672731960686817913 10898869254548970515113435)
          ·
            refine ⟨16348303881823455772670153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10898869254548970515113435 16348303881823455772670153)
            ·
              refine ⟨12261227911367591829502615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16348303881823455772670153 12261227911367591829502615)
              ·
                refine ⟨18391841867051387744253923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12261227911367591829502615 18391841867051387744253923)
                ·
                  refine ⟨27587762800577081616380885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18391841867051387744253923 27587762800577081616380885)
                  ·
                    refine ⟨646588190638525350383927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27587762800577081616380885 646588190638525350383927)
                    ·
                      rfl

theorem cell23_3777678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_3777678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777678 prefixEnd_3777678 := by exact prefixLift 3777678
  have htrace : WordTrace (prefixWord ++ tailWord_3777678) baseStart_3777678 baseEnd_3777678 := by
    simpa [prefixWord, tailWord_3777678, baseEnd_3777678] using wordTrace_append hprefix tailTrace_3777678
  have hstable : (prefixWord ++ tailWord_3777678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777678).length < 2 ^ (prefixWord ++ tailWord_3777678).sum := by decide
  have hdescent : baseEnd_3777678 < baseStart_3777678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777682 : List Nat := [3, 2, 3, 1, 1, 4, 1, 3, 5]
def baseStart_3777682 : Nat := 118140960795 + 3777682 * 2 ^ 59
def prefixEnd_3777682 : Nat := 4983230072969 + 3 ^ 40 * 3777682 * 2
def baseEnd_3777682 : Nat := 215529625093132670611307

theorem tailTrace_3777682 : CollatzResearch.WordTrace tailWord_3777682 prefixEnd_3777682 215529625093132670611307 := by
  unfold tailWord_3777682
  simp only [CollatzResearch.WordTrace]
  refine ⟨34445845475027691391391825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91855587933407177043711533 34445845475027691391391825)
  ·
    refine ⟨25834384106270768543543869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34445845475027691391391825 25834384106270768543543869)
    ·
      refine ⟨9687894039851538203828951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25834384106270768543543869 9687894039851538203828951)
      ·
        refine ⟨14531841059777307305743427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9687894039851538203828951 14531841059777307305743427)
        ·
          refine ⟨21797761589665960958615141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14531841059777307305743427 21797761589665960958615141)
          ·
            refine ⟨4087080298062367679740339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21797761589665960958615141 4087080298062367679740339)
            ·
              refine ⟨6130620447093551519610509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4087080298062367679740339 6130620447093551519610509)
              ·
                refine ⟨2298982667660081819853941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6130620447093551519610509 2298982667660081819853941)
                ·
                  refine ⟨215529625093132670611307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2298982667660081819853941 215529625093132670611307)
                  ·
                    rfl

theorem cell23_3777682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 3, 5].length) (baseStart_3777682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777682 prefixEnd_3777682 := by exact prefixLift 3777682
  have htrace : WordTrace (prefixWord ++ tailWord_3777682) baseStart_3777682 baseEnd_3777682 := by
    simpa [prefixWord, tailWord_3777682, baseEnd_3777682] using wordTrace_append hprefix tailTrace_3777682
  have hstable : (prefixWord ++ tailWord_3777682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777682).length < 2 ^ (prefixWord ++ tailWord_3777682).sum := by decide
  have hdescent : baseEnd_3777682 < baseStart_3777682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777695 : List Nat := [1, 1, 2, 6, 2, 1, 1, 2, 2, 5]
def baseStart_3777695 : Nat := 118140960795 + 3777695 * 2 ^ 59
def prefixEnd_3777695 : Nat := 4983230072969 + 3 ^ 40 * 3777695 * 2
def baseEnd_3777695 : Nat := 646591100362234161546401

theorem tailTrace_3777695 : CollatzResearch.WordTrace tailWord_3777695 prefixEnd_3777695 646591100362234161546401 := by
  unfold tailWord_3777695
  simp only [CollatzResearch.WordTrace]
  refine ⟨137783856049063668785790539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91855904032709112523860359 137783856049063668785790539)
  ·
    refine ⟨206675784073595503178685809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137783856049063668785790539 206675784073595503178685809)
    ·
      refine ⟨155006838055196627384014357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206675784073595503178685809 155006838055196627384014357)
      ·
        refine ⟨7265945533837341908625673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 155006838055196627384014357 7265945533837341908625673)
        ·
          refine ⟨5449459150378006431469255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7265945533837341908625673 5449459150378006431469255)
          ·
            refine ⟨8174188725567009647203883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5449459150378006431469255 8174188725567009647203883)
            ·
              refine ⟨12261283088350514470805825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8174188725567009647203883 12261283088350514470805825)
              ·
                refine ⟨9195962316262885853104369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12261283088350514470805825 9195962316262885853104369)
                ·
                  refine ⟨6896971737197164389828277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9195962316262885853104369 6896971737197164389828277)
                  ·
                    refine ⟨646591100362234161546401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6896971737197164389828277 646591100362234161546401)
                    ·
                      rfl

theorem cell23_3777695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 5].length) (baseStart_3777695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777695 prefixEnd_3777695 := by exact prefixLift 3777695
  have htrace : WordTrace (prefixWord ++ tailWord_3777695) baseStart_3777695 baseEnd_3777695 := by
    simpa [prefixWord, tailWord_3777695, baseEnd_3777695] using wordTrace_append hprefix tailTrace_3777695
  have hstable : (prefixWord ++ tailWord_3777695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777695).length < 2 ^ (prefixWord ++ tailWord_3777695).sum := by decide
  have hdescent : baseEnd_3777695 < baseStart_3777695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777708 : List Nat := [2, 2, 1, 1, 1, 1, 1, 7, 3, 4]
def baseStart_3777708 : Nat := 118140960795 + 3777708 * 2 ^ 59
def prefixEnd_3777708 : Nat := 4983230072969 + 3 ^ 40 * 3777708 * 2
def baseEnd_3777708 : Nat := 646593325445070311258881

theorem tailTrace_3777708 : CollatzResearch.WordTrace tailWord_3777708 prefixEnd_3777708 646593325445070311258881 := by
  unfold tailWord_3777708
  simp only [CollatzResearch.WordTrace]
  refine ⟨68892165099008286003006889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91856220132011048004009185 68892165099008286003006889)
  ·
    refine ⟨51669123824256214502255167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68892165099008286003006889 51669123824256214502255167)
    ·
      refine ⟨77503685736384321753382751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51669123824256214502255167 77503685736384321753382751)
      ·
        refine ⟨116255528604576482630074127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77503685736384321753382751 116255528604576482630074127)
        ·
          refine ⟨174383292906864723945111191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116255528604576482630074127 174383292906864723945111191)
          ·
            refine ⟨261574939360297085917666787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174383292906864723945111191 261574939360297085917666787)
            ·
              refine ⟨392362409040445628876500181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261574939360297085917666787 392362409040445628876500181)
              ·
                refine ⟨9195993961885444426792973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 392362409040445628876500181 9195993961885444426792973)
                ·
                  refine ⟨3448497735707041660047365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9195993961885444426792973 3448497735707041660047365)
                  ·
                    refine ⟨646593325445070311258881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3448497735707041660047365 646593325445070311258881)
                    ·
                      rfl

theorem cell23_3777708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 4].length) (baseStart_3777708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777708 prefixEnd_3777708 := by exact prefixLift 3777708
  have htrace : WordTrace (prefixWord ++ tailWord_3777708) baseStart_3777708 baseEnd_3777708 := by
    simpa [prefixWord, tailWord_3777708, baseEnd_3777708] using wordTrace_append hprefix tailTrace_3777708
  have hstable : (prefixWord ++ tailWord_3777708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777708).length < 2 ^ (prefixWord ++ tailWord_3777708).sum := by decide
  have hdescent : baseEnd_3777708 < baseStart_3777708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777711 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 6]
def baseStart_3777711 : Nat := 118140960795 + 3777711 * 2 ^ 59
def prefixEnd_3777711 : Nat := 4983230072969 + 3 ^ 40 * 3777711 * 2
def baseEnd_3777711 : Nat := 1939781516777174422039129

theorem tailTrace_3777711 : CollatzResearch.WordTrace tailWord_3777711 prefixEnd_3777711 1939781516777174422039129 := by
  unfold tailWord_3777711
  simp only [CollatzResearch.WordTrace]
  refine ⟨137784439617005703518372987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91856293078003802345581991 137784439617005703518372987)
  ·
    refine ⟨206676659425508555277559481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137784439617005703518372987 206676659425508555277559481)
    ·
      refine ⟨155007494569131416458169611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206676659425508555277559481 155007494569131416458169611)
      ·
        refine ⟨232511241853697124687254417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155007494569131416458169611 232511241853697124687254417)
        ·
          refine ⟨174383431390272843515440813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232511241853697124687254417 174383431390272843515440813)
          ·
            refine ⟨65393786771352316318290305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174383431390272843515440813 65393786771352316318290305)
            ·
              refine ⟨49045340078514237238717729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65393786771352316318290305 49045340078514237238717729)
              ·
                refine ⟨36784005058885677929038297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49045340078514237238717729 36784005058885677929038297)
                ·
                  refine ⟨27588003794164258446778723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36784005058885677929038297 27588003794164258446778723)
                  ·
                    refine ⟨41382005691246387670168085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27588003794164258446778723 41382005691246387670168085)
                    ·
                      refine ⟨1939781516777174422039129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41382005691246387670168085 1939781516777174422039129)
                      ·
                        rfl

theorem cell23_3777711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 6].length) (baseStart_3777711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777711 prefixEnd_3777711 := by exact prefixLift 3777711
  have htrace : WordTrace (prefixWord ++ tailWord_3777711) baseStart_3777711 baseEnd_3777711 := by
    simpa [prefixWord, tailWord_3777711, baseEnd_3777711] using wordTrace_append hprefix tailTrace_3777711
  have hstable : (prefixWord ++ tailWord_3777711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777711).length < 2 ^ (prefixWord ++ tailWord_3777711).sum := by decide
  have hdescent : baseEnd_3777711 < baseStart_3777711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777732 : List Nat := [2, 3, 3, 1, 3, 1, 2, 1, 2, 1, 4]
def baseStart_3777732 : Nat := 118140960795 + 3777732 * 2 ^ 59
def prefixEnd_3777732 : Nat := 4983230072969 + 3 ^ 40 * 3777732 * 2
def baseEnd_3777732 : Nat := 1939792299870918839876533

theorem tailTrace_3777732 : CollatzResearch.WordTrace tailWord_3777732 prefixEnd_3777732 1939792299870918839876533 := by
  unfold tailWord_3777732
  simp only [CollatzResearch.WordTrace]
  refine ⟨68892602774964812052443725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91856803699953082736591633 68892602774964812052443725)
  ·
    refine ⟨25834726040611804519666397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68892602774964812052443725 25834726040611804519666397)
    ·
      refine ⟨9688022265229426694874899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25834726040611804519666397 9688022265229426694874899)
      ·
        refine ⟨14532033397844140042312349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9688022265229426694874899 14532033397844140042312349)
        ·
          refine ⟨5449512524191552515867131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14532033397844140042312349 5449512524191552515867131)
          ·
            refine ⟨8174268786287328773800697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5449512524191552515867131 8174268786287328773800697)
            ·
              refine ⟨6130701589715496580350523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8174268786287328773800697 6130701589715496580350523)
              ·
                refine ⟨9196052384573244870525785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6130701589715496580350523 9196052384573244870525785)
                ·
                  refine ⟨6897039288429933652894339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9196052384573244870525785 6897039288429933652894339)
                  ·
                    refine ⟨10345558932644900479341509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6897039288429933652894339 10345558932644900479341509)
                    ·
                      refine ⟨1939792299870918839876533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10345558932644900479341509 1939792299870918839876533)
                      ·
                        rfl

theorem cell23_3777732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_3777732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777732 prefixEnd_3777732 := by exact prefixLift 3777732
  have htrace : WordTrace (prefixWord ++ tailWord_3777732) baseStart_3777732 baseEnd_3777732 := by
    simpa [prefixWord, tailWord_3777732, baseEnd_3777732] using wordTrace_append hprefix tailTrace_3777732
  have hstable : (prefixWord ++ tailWord_3777732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777732).length < 2 ^ (prefixWord ++ tailWord_3777732).sum := by decide
  have hdescent : baseEnd_3777732 < baseStart_3777732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777768 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 5, 5]
def baseStart_3777768 : Nat := 118140960795 + 3777768 * 2 ^ 59
def prefixEnd_3777768 : Nat := 4983230072969 + 3 ^ 40 * 3777768 * 2
def baseEnd_3777768 : Nat := 646603595058160233008789

theorem tailTrace_3777768 : CollatzResearch.WordTrace tailWord_3777768 prefixEnd_3777768 646603595058160233008789 := by
  unfold tailWord_3777768
  simp only [CollatzResearch.WordTrace]
  refine ⟨68893259288899601126598979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91857679051866134835465305 68893259288899601126598979)
  ·
    refine ⟨103339888933349401689898469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68893259288899601126598979 103339888933349401689898469)
    ·
      refine ⟨19376229175003012816855963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103339888933349401689898469 19376229175003012816855963)
      ·
        refine ⟨29064343762504519225283945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19376229175003012816855963 29064343762504519225283945)
        ·
          refine ⟨21798257821878389418962959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29064343762504519225283945 21798257821878389418962959)
          ·
            refine ⟨32697386732817584128444439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21798257821878389418962959 32697386732817584128444439)
            ·
              refine ⟨49046080099226376192666659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32697386732817584128444439 49046080099226376192666659)
              ·
                refine ⟨73569120148839564288999989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49046080099226376192666659 73569120148839564288999989)
                ·
                  refine ⟨6897105013953709152093749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73569120148839564288999989 6897105013953709152093749)
                  ·
                    refine ⟨646603595058160233008789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6897105013953709152093749 646603595058160233008789)
                    ·
                      rfl

theorem cell23_3777768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_3777768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777768 prefixEnd_3777768 := by exact prefixLift 3777768
  have htrace : WordTrace (prefixWord ++ tailWord_3777768) baseStart_3777768 baseEnd_3777768 := by
    simpa [prefixWord, tailWord_3777768, baseEnd_3777768] using wordTrace_append hprefix tailTrace_3777768
  have hstable : (prefixWord ++ tailWord_3777768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777768).length < 2 ^ (prefixWord ++ tailWord_3777768).sum := by decide
  have hdescent : baseEnd_3777768 < baseStart_3777768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777815 : List Nat := [1, 1, 3, 4, 1, 1, 3, 1, 4, 4]
def baseStart_3777815 : Nat := 118140960795 + 3777815 * 2 ^ 59
def prefixEnd_3777815 : Nat := 4983230072969 + 3 ^ 40 * 3777815 * 2
def baseEnd_3777815 : Nat := 646611639588414005046217

theorem tailTrace_3777815 : CollatzResearch.WordTrace tailWord_3777815 prefixEnd_3777815 646611639588414005046217 := by
  unfold tailWord_3777815
  simp only [CollatzResearch.WordTrace]
  refine ⟨137788232808628929280158899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91858821872419286186772599 137788232808628929280158899)
  ·
    refine ⟨206682349212943393920238349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137788232808628929280158899 206682349212943393920238349)
    ·
      refine ⟨77505880954853772720089381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206682349212943393920238349 77505880954853772720089381)
      ·
        refine ⟨14532352679035082385016759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77505880954853772720089381 14532352679035082385016759)
        ·
          refine ⟨21798529018552623577525139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14532352679035082385016759 21798529018552623577525139)
          ·
            refine ⟨32697793527828935366287709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21798529018552623577525139 32697793527828935366287709)
            ·
              refine ⟨12261672572935850762357891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32697793527828935366287709 12261672572935850762357891)
              ·
                refine ⟨18392508859403776143536837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12261672572935850762357891 18392508859403776143536837)
                ·
                  refine ⟨3448595411138208026913157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18392508859403776143536837 3448595411138208026913157)
                  ·
                    refine ⟨646611639588414005046217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3448595411138208026913157 646611639588414005046217)
                    ·
                      rfl

theorem cell23_3777815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 4, 4].length) (baseStart_3777815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777815 prefixEnd_3777815 := by exact prefixLift 3777815
  have htrace : WordTrace (prefixWord ++ tailWord_3777815) baseStart_3777815 baseEnd_3777815 := by
    simpa [prefixWord, tailWord_3777815, baseEnd_3777815] using wordTrace_append hprefix tailTrace_3777815
  have hstable : (prefixWord ++ tailWord_3777815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777815).length < 2 ^ (prefixWord ++ tailWord_3777815).sum := by decide
  have hdescent : baseEnd_3777815 < baseStart_3777815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777828 : List Nat := [2, 3, 1, 3, 1, 1, 2, 10]
def baseStart_3777828 : Nat := 118140960795 + 3777828 * 2 ^ 59
def prefixEnd_3777828 : Nat := 4983230072969 + 3 ^ 40 * 3777828 * 2
def baseEnd_3777828 : Nat := 71845984963472239417633

theorem tailTrace_3777828 : CollatzResearch.WordTrace tailWord_3777828 prefixEnd_3777828 71845984963472239417633 := by
  unfold tailWord_3777828
  simp only [CollatzResearch.WordTrace]
  refine ⟨68894353478790916250191069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91859137971721221666921425 68894353478790916250191069)
  ·
    refine ⟨25835382554546593593821651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68894353478790916250191069 25835382554546593593821651)
    ·
      refine ⟨38753073831819890390732477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25835382554546593593821651 38753073831819890390732477)
      ·
        refine ⟨14532402686932458896524679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38753073831819890390732477 14532402686932458896524679)
        ·
          refine ⟨21798604030398688344787019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14532402686932458896524679 21798604030398688344787019)
          ·
            refine ⟨32697906045598032517180529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21798604030398688344787019 32697906045598032517180529)
            ·
              refine ⟨24523429534198524387885397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32697906045598032517180529 24523429534198524387885397)
              ·
                refine ⟨71845984963472239417633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 24523429534198524387885397 71845984963472239417633)
                ·
                  rfl

theorem cell23_3777828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 10].length) (baseStart_3777828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777828 prefixEnd_3777828 := by exact prefixLift 3777828
  have htrace : WordTrace (prefixWord ++ tailWord_3777828) baseStart_3777828 baseEnd_3777828 := by
    simpa [prefixWord, tailWord_3777828, baseEnd_3777828] using wordTrace_append hprefix tailTrace_3777828
  have hstable : (prefixWord ++ tailWord_3777828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777828).length < 2 ^ (prefixWord ++ tailWord_3777828).sum := by decide
  have hdescent : baseEnd_3777828 < baseStart_3777828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777832 : List Nat := [2, 1, 5, 1, 2, 3, 1, 1, 1, 6]
def baseStart_3777832 : Nat := 118140960795 + 3777832 * 2 ^ 59
def prefixEnd_3777832 : Nat := 4983230072969 + 3 ^ 40 * 3777832 * 2
def baseEnd_3777832 : Nat := 646614549312122816208691

theorem tailTrace_3777832 : CollatzResearch.WordTrace tailWord_3777832 prefixEnd_3777832 646614549312122816208691 := by
  unfold tailWord_3777832
  simp only [CollatzResearch.WordTrace]
  refine ⟨68894426424783670591763875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91859235233044894122351833 68894426424783670591763875)
  ·
    refine ⟨103341639637175505887645813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68894426424783670591763875 103341639637175505887645813)
    ·
      refine ⟨9688278715985203676966795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103341639637175505887645813 9688278715985203676966795)
      ·
        refine ⟨14532418073977805515450193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9688278715985203676966795 14532418073977805515450193)
        ·
          refine ⟨10899313555483354136587645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14532418073977805515450193 10899313555483354136587645)
          ·
            refine ⟨4087242583306257801220367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10899313555483354136587645 4087242583306257801220367)
            ·
              refine ⟨6130863874959386701830551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4087242583306257801220367 6130863874959386701830551)
              ·
                refine ⟨9196295812439080052745827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6130863874959386701830551 9196295812439080052745827)
                ·
                  refine ⟨13794443718658620079118741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9196295812439080052745827 13794443718658620079118741)
                  ·
                    refine ⟨646614549312122816208691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13794443718658620079118741 646614549312122816208691)
                    ·
                      rfl

theorem cell23_3777832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_3777832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777832 prefixEnd_3777832 := by exact prefixLift 3777832
  have htrace : WordTrace (prefixWord ++ tailWord_3777832) baseStart_3777832 baseEnd_3777832 := by
    simpa [prefixWord, tailWord_3777832, baseEnd_3777832] using wordTrace_append hprefix tailTrace_3777832
  have hstable : (prefixWord ++ tailWord_3777832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777832).length < 2 ^ (prefixWord ++ tailWord_3777832).sum := by decide
  have hdescent : baseEnd_3777832 < baseStart_3777832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777842 : List Nat := [3, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3]
def baseStart_3777842 : Nat := 118140960795 + 3777842 * 2 ^ 59
def prefixEnd_3777842 : Nat := 4983230072969 + 3 ^ 40 * 3777842 * 2
def baseEnd_3777842 : Nat := 1939848782742913409501027

theorem tailTrace_3777842 : CollatzResearch.WordTrace tailWord_3777842 prefixEnd_3777842 1939848782742913409501027 := by
  unfold tailWord_3777842
  simp only [CollatzResearch.WordTrace]
  refine ⟨34447304394882778222847945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91859478386354075260927853 34447304394882778222847945)
  ·
    refine ⟨25835478296162083667135959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34447304394882778222847945 25835478296162083667135959)
    ·
      refine ⟨38753217444243125500703939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25835478296162083667135959 38753217444243125500703939)
      ·
        refine ⟨58129826166364688251055909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38753217444243125500703939 58129826166364688251055909)
        ·
          refine ⟨10899342406193379047072983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58129826166364688251055909 10899342406193379047072983)
          ·
            refine ⟨16349013609290068570609475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10899342406193379047072983 16349013609290068570609475)
            ·
              refine ⟨24523520413935102855914213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16349013609290068570609475 24523520413935102855914213)
              ·
                refine ⟨4598160077612831785483915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24523520413935102855914213 4598160077612831785483915)
                ·
                  refine ⟨6897240116419247678225873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4598160077612831785483915 6897240116419247678225873)
                  ·
                    refine ⟨5172930087314435758669405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6897240116419247678225873 5172930087314435758669405)
                    ·
                      refine ⟨1939848782742913409501027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5172930087314435758669405 1939848782742913409501027)
                      ·
                        rfl

theorem cell23_3777842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_3777842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777842 prefixEnd_3777842 := by exact prefixLift 3777842
  have htrace : WordTrace (prefixWord ++ tailWord_3777842) baseStart_3777842 baseEnd_3777842 := by
    simpa [prefixWord, tailWord_3777842, baseEnd_3777842] using wordTrace_append hprefix tailTrace_3777842
  have hstable : (prefixWord ++ tailWord_3777842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777842).length < 2 ^ (prefixWord ++ tailWord_3777842).sum := by decide
  have hdescent : baseEnd_3777842 < baseStart_3777842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777845 : List Nat := [1, 3, 3, 1, 2, 2, 4, 7]
def baseStart_3777845 : Nat := 118140960795 + 3777845 * 2 ^ 59
def prefixEnd_3777845 : Nat := 4983230072969 + 3 ^ 40 * 3777845 * 2
def baseEnd_3777845 : Nat := 71846308266106551769019

theorem tailTrace_3777845 : CollatzResearch.WordTrace tailWord_3777845 prefixEnd_3777845 71846308266106551769019 := by
  unfold tailWord_3777845
  simp only [CollatzResearch.WordTrace]
  refine ⟨137789326998520244403750989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91859551332346829602500659 137789326998520244403750989)
  ·
    refine ⟨51670997624445091651406621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137789326998520244403750989 51670997624445091651406621)
    ·
      refine ⟨19376624109166909369277483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51670997624445091651406621 19376624109166909369277483)
      ·
        refine ⟨29064936163750364053916225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19376624109166909369277483 29064936163750364053916225)
        ·
          refine ⟨21798702122812773040437169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29064936163750364053916225 21798702122812773040437169)
          ·
            refine ⟨16349026592109579780327877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21798702122812773040437169 16349026592109579780327877)
            ·
              refine ⟨3065442486020546208811477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16349026592109579780327877 3065442486020546208811477)
              ·
                refine ⟨71846308266106551769019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3065442486020546208811477 71846308266106551769019)
                ·
                  rfl

theorem cell23_3777845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 7].length) (baseStart_3777845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777845 prefixEnd_3777845 := by exact prefixLift 3777845
  have htrace : WordTrace (prefixWord ++ tailWord_3777845) baseStart_3777845 baseEnd_3777845 := by
    simpa [prefixWord, tailWord_3777845, baseEnd_3777845] using wordTrace_append hprefix tailTrace_3777845
  have hstable : (prefixWord ++ tailWord_3777845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777845).length < 2 ^ (prefixWord ++ tailWord_3777845).sum := by decide
  have hdescent : baseEnd_3777845 < baseStart_3777845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777872 : List Nat := [2, 1, 1, 1, 1, 5, 2, 4, 2, 1, 3]
def baseStart_3777872 : Nat := 118140960795 + 3777872 * 2 ^ 59
def prefixEnd_3777872 : Nat := 4983230072969 + 3 ^ 40 * 3777872 * 2
def baseEnd_3777872 : Nat := 1939864187162548292125889

theorem tailTrace_3777872 : CollatzResearch.WordTrace tailWord_3777872 prefixEnd_3777872 1939864187162548292125889 := by
  unfold tailWord_3777872
  simp only [CollatzResearch.WordTrace]
  refine ⟨68895155884711214007491935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91860207846281618676655913 68895155884711214007491935)
  ·
    refine ⟨103342733827066821011237903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68895155884711214007491935 103342733827066821011237903)
    ·
      refine ⟨155014100740600231516856855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103342733827066821011237903 155014100740600231516856855)
      ·
        refine ⟨232521151110900347275285283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155014100740600231516856855 232521151110900347275285283)
        ·
          refine ⟨348781726666350520912927925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232521151110900347275285283 348781726666350520912927925)
          ·
            refine ⟨32698286874970361335586993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 348781726666350520912927925 32698286874970361335586993)
            ·
              refine ⟨24523715156227771001690245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32698286874970361335586993 24523715156227771001690245)
              ·
                refine ⟨4598196591792707062816921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24523715156227771001690245 4598196591792707062816921)
                ·
                  refine ⟨3448647443844530297112691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4598196591792707062816921 3448647443844530297112691)
                  ·
                    refine ⟨5172971165766795445669037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3448647443844530297112691 5172971165766795445669037)
                    ·
                      refine ⟨1939864187162548292125889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5172971165766795445669037 1939864187162548292125889)
                      ·
                        rfl

theorem cell23_3777872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 2, 1, 3].length) (baseStart_3777872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777872 prefixEnd_3777872 := by exact prefixLift 3777872
  have htrace : WordTrace (prefixWord ++ tailWord_3777872) baseStart_3777872 baseEnd_3777872 := by
    simpa [prefixWord, tailWord_3777872, baseEnd_3777872] using wordTrace_append hprefix tailTrace_3777872
  have hstable : (prefixWord ++ tailWord_3777872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777872).length < 2 ^ (prefixWord ++ tailWord_3777872).sum := by decide
  have hdescent : baseEnd_3777872 < baseStart_3777872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777945 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 1, 5, 3]
def baseStart_3777945 : Nat := 118140960795 + 3777945 * 2 ^ 59
def prefixEnd_3777945 : Nat := 4983230072969 + 3 ^ 40 * 3777945 * 2
def baseEnd_3777945 : Nat := 1939901671250326506513053

theorem tailTrace_3777945 : CollatzResearch.WordTrace tailWord_3777945 prefixEnd_3777945 1939901671250326506513053 := by
  unfold tailWord_3777945
  simp only [CollatzResearch.WordTrace]
  refine ⟨137792974298157961482391289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91861982865438640988260859 137792974298157961482391289)
  ·
    refine ⟨103344730723618471111793467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137792974298157961482391289 103344730723618471111793467)
    ·
      refine ⟨155017096085427706667690201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103344730723618471111793467 155017096085427706667690201)
      ·
        refine ⟨116262822064070780000767651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155017096085427706667690201 116262822064070780000767651)
        ·
          refine ⟨174394233096106170001151477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116262822064070780000767651 174394233096106170001151477)
          ·
            refine ⟨16349459352759953437607951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 174394233096106170001151477 16349459352759953437607951)
            ·
              refine ⟨24524189029139930156411927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16349459352759953437607951 24524189029139930156411927)
              ·
                refine ⟨36786283543709895234617891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24524189029139930156411927 36786283543709895234617891)
                ·
                  refine ⟨55179425315564842851926837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36786283543709895234617891 55179425315564842851926837)
                  ·
                    refine ⟨5173071123334204017368141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55179425315564842851926837 5173071123334204017368141)
                    ·
                      refine ⟨1939901671250326506513053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5173071123334204017368141 1939901671250326506513053)
                      ·
                        rfl

theorem cell23_3777945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 5, 3].length) (baseStart_3777945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777945 prefixEnd_3777945 := by exact prefixLift 3777945
  have htrace : WordTrace (prefixWord ++ tailWord_3777945) baseStart_3777945 baseEnd_3777945 := by
    simpa [prefixWord, tailWord_3777945, baseEnd_3777945] using wordTrace_append hprefix tailTrace_3777945
  have hstable : (prefixWord ++ tailWord_3777945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777945).length < 2 ^ (prefixWord ++ tailWord_3777945).sum := by decide
  have hdescent : baseEnd_3777945 < baseStart_3777945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3777980 : List Nat := [2, 2, 2, 4, 3, 1, 1, 2, 2, 2, 2]
def baseStart_3777980 : Nat := 118140960795 + 3777980 * 2 ^ 59
def prefixEnd_3777980 : Nat := 4983230072969 + 3 ^ 40 * 3777980 * 2
def baseEnd_3777980 : Nat := 1939919643073233869575393

theorem tailTrace_3777980 : CollatzResearch.WordTrace tailWord_3777980 prefixEnd_3777980 1939919643073233869575393 := by
  unfold tailWord_3777980
  simp only [CollatzResearch.WordTrace]
  refine ⟨68897125426515581229957697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91862833902020774973276929 68897125426515581229957697)
  ·
    refine ⟨51672844069886685922468273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68897125426515581229957697 51672844069886685922468273)
    ·
      refine ⟨38754633052415014441851205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51672844069886685922468273 38754633052415014441851205)
      ·
        refine ⟨7266493697327815207847101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38754633052415014441851205 7266493697327815207847101)
        ·
          refine ⟨2724935136497930702942663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7266493697327815207847101 2724935136497930702942663)
          ·
            refine ⟨4087402704746896054413995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2724935136497930702942663 4087402704746896054413995)
            ·
              refine ⟨6131104057120344081620993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4087402704746896054413995 6131104057120344081620993)
              ·
                refine ⟨4598328042840258061215745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6131104057120344081620993 4598328042840258061215745)
                ·
                  refine ⟨3448746032130193545911809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4598328042840258061215745 3448746032130193545911809)
                  ·
                    refine ⟨2586559524097645159433857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3448746032130193545911809 2586559524097645159433857)
                    ·
                      refine ⟨1939919643073233869575393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2586559524097645159433857 1939919643073233869575393)
                      ·
                        rfl

theorem cell23_3777980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_3777980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3777980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3777980 prefixEnd_3777980 := by exact prefixLift 3777980
  have htrace : WordTrace (prefixWord ++ tailWord_3777980) baseStart_3777980 baseEnd_3777980 := by
    simpa [prefixWord, tailWord_3777980, baseEnd_3777980] using wordTrace_append hprefix tailTrace_3777980
  have hstable : (prefixWord ++ tailWord_3777980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3777980).length < 2 ^ (prefixWord ++ tailWord_3777980).sum := by decide
  have hdescent : baseEnd_3777980 < baseStart_3777980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3777980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778015 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 4]
def baseStart_3778015 : Nat := 118140960795 + 3778015 * 2 ^ 59
def prefixEnd_3778015 : Nat := 4983230072969 + 3 ^ 40 * 3778015 * 2
def baseEnd_3778015 : Nat := 1939937614896141232637731

theorem tailTrace_3778015 : CollatzResearch.WordTrace tailWord_3778015 prefixEnd_3778015 1939937614896141232637731 := by
  unfold tailWord_3778015
  simp only [CollatzResearch.WordTrace]
  refine ⟨137795527407904363437439499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91863684938602908958292999 137795527407904363437439499)
  ·
    refine ⟨206693291111856545156159249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137795527407904363437439499 206693291111856545156159249)
    ·
      refine ⟨155019968333892408867119437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206693291111856545156159249 155019968333892408867119437)
      ·
        refine ⟨58132488125209653325169789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155019968333892408867119437 58132488125209653325169789)
        ·
          refine ⟨21799683046953619996938671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58132488125209653325169789 21799683046953619996938671)
          ·
            refine ⟨32699524570430429995408007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21799683046953619996938671 32699524570430429995408007)
            ·
              refine ⟨49049286855645644993112011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32699524570430429995408007 49049286855645644993112011)
              ·
                refine ⟨73573930283468467489668017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49049286855645644993112011 73573930283468467489668017)
                ·
                  refine ⟨55180447712601350617251013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73573930283468467489668017 55180447712601350617251013)
                  ·
                    refine ⟨10346333946112753240734565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55180447712601350617251013 10346333946112753240734565)
                    ·
                      refine ⟨1939937614896141232637731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10346333946112753240734565 1939937614896141232637731)
                      ·
                        rfl

theorem cell23_3778015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_3778015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3778015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3778015 prefixEnd_3778015 := by exact prefixLift 3778015
  have htrace : WordTrace (prefixWord ++ tailWord_3778015) baseStart_3778015 baseEnd_3778015 := by
    simpa [prefixWord, tailWord_3778015, baseEnd_3778015] using wordTrace_append hprefix tailTrace_3778015
  have hstable : (prefixWord ++ tailWord_3778015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778015).length < 2 ^ (prefixWord ++ tailWord_3778015).sum := by decide
  have hdescent : baseEnd_3778015 < baseStart_3778015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778079 : List Nat := [1, 1, 2, 4, 1, 1, 3, 3, 2, 3, 2]
def baseStart_3778079 : Nat := 118140960795 + 3778079 * 2 ^ 59
def prefixEnd_3778079 : Nat := 4983230072969 + 3 ^ 40 * 3778079 * 2
def baseEnd_3778079 : Nat := 1939970477658028982237437

theorem tailTrace_3778079 : CollatzResearch.WordTrace tailWord_3778079 prefixEnd_3778079 1939970477658028982237437 := by
  unfold tailWord_3778079
  simp only [CollatzResearch.WordTrace]
  refine ⟨137797861679672502367769291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91865241119781668245179527 137797861679672502367769291)
  ·
    refine ⟨206696792519508753551653937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137797861679672502367769291 206696792519508753551653937)
    ·
      refine ⟨155022594389631565163740453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206696792519508753551653937 155022594389631565163740453)
      ·
        refine ⟨29066736448055918468201335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155022594389631565163740453 29066736448055918468201335)
        ·
          refine ⟨43600104672083877702302003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29066736448055918468201335 43600104672083877702302003)
          ·
            refine ⟨65400157008125816553453005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43600104672083877702302003 65400157008125816553453005)
            ·
              refine ⟨24525058878047181207544877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65400157008125816553453005 24525058878047181207544877)
              ·
                refine ⟨9196897079267692952829329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24525058878047181207544877 9196897079267692952829329)
                ·
                  refine ⟨6897672809450769714621997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9196897079267692952829329 6897672809450769714621997)
                  ·
                    refine ⟨2586627303544038642983249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6897672809450769714621997 2586627303544038642983249)
                    ·
                      refine ⟨1939970477658028982237437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2586627303544038642983249 1939970477658028982237437)
                      ·
                        rfl

theorem cell23_3778079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_3778079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3778079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3778079 prefixEnd_3778079 := by exact prefixLift 3778079
  have htrace : WordTrace (prefixWord ++ tailWord_3778079) baseStart_3778079 baseEnd_3778079 := by
    simpa [prefixWord, tailWord_3778079, baseEnd_3778079] using wordTrace_append hprefix tailTrace_3778079
  have hstable : (prefixWord ++ tailWord_3778079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778079).length < 2 ^ (prefixWord ++ tailWord_3778079).sum := by decide
  have hdescent : baseEnd_3778079 < baseStart_3778079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778103 : List Nat := [1, 1, 3, 1, 2, 4, 4, 2, 1, 1, 3]
def baseStart_3778103 : Nat := 118140960795 + 3778103 * 2 ^ 59
def prefixEnd_3778103 : Nat := 4983230072969 + 3 ^ 40 * 3778103 * 2
def baseEnd_3778103 : Nat := 1939982801193736888337327

theorem tailTrace_3778103 : CollatzResearch.WordTrace tailWord_3778103 prefixEnd_3778103 1939982801193736888337327 := by
  unfold tailWord_3778103
  simp only [CollatzResearch.WordTrace]
  refine ⟨137798737031585554466642963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91865824687723702977761975 137798737031585554466642963)
  ·
    refine ⟨206698105547378331699964445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137798737031585554466642963 206698105547378331699964445)
    ·
      refine ⟨77511789580266874387486667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206698105547378331699964445 77511789580266874387486667)
      ·
        refine ⟨116267684370400311581230001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77511789580266874387486667 116267684370400311581230001)
        ·
          refine ⟨87200763277800233685922501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116267684370400311581230001 87200763277800233685922501)
          ·
            refine ⟨16350143114587543816110469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87200763277800233685922501 16350143114587543816110469)
            ·
              refine ⟨3065651833985164465520713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16350143114587543816110469 3065651833985164465520713)
              ·
                refine ⟨2299238875488873349140535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3065651833985164465520713 2299238875488873349140535)
                ·
                  refine ⟨3448858313233310023710803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2299238875488873349140535 3448858313233310023710803)
                  ·
                    refine ⟨5173287469849965035566205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3448858313233310023710803 5173287469849965035566205)
                    ·
                      refine ⟨1939982801193736888337327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5173287469849965035566205 1939982801193736888337327)
                      ·
                        rfl

theorem cell23_3778103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 2, 1, 1, 3].length) (baseStart_3778103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3778103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3778103 prefixEnd_3778103 := by exact prefixLift 3778103
  have htrace : WordTrace (prefixWord ++ tailWord_3778103) baseStart_3778103 baseEnd_3778103 := by
    simpa [prefixWord, tailWord_3778103, baseEnd_3778103] using wordTrace_append hprefix tailTrace_3778103
  have hstable : (prefixWord ++ tailWord_3778103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778103).length < 2 ^ (prefixWord ++ tailWord_3778103).sum := by decide
  have hdescent : baseEnd_3778103 < baseStart_3778103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778119 : List Nat := [1, 1, 4, 1, 5, 1, 2, 1, 1, 6]
def baseStart_3778119 : Nat := 118140960795 + 3778119 * 2 ^ 59
def prefixEnd_3778119 : Nat := 4983230072969 + 3 ^ 40 * 3778119 * 2
def baseEnd_3778119 : Nat := 646663672294736275245751

theorem tailTrace_3778119 : CollatzResearch.WordTrace tailWord_3778119 prefixEnd_3778119 646663672294736275245751 := by
  unfold tailWord_3778119
  simp only [CollatzResearch.WordTrace]
  refine ⟨137799320599527589199225411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91866213733018392799483607 137799320599527589199225411)
  ·
    refine ⟨206698980899291383798838117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137799320599527589199225411 206698980899291383798838117)
    ·
      refine ⟨38756058918617134462282147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206698980899291383798838117 38756058918617134462282147)
      ·
        refine ⟨58134088377925701693423221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38756058918617134462282147 58134088377925701693423221)
        ·
          refine ⟨5450070785430534533758427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58134088377925701693423221 5450070785430534533758427)
          ·
            refine ⟨8175106178145801800637641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5450070785430534533758427 8175106178145801800637641)
            ·
              refine ⟨6131329633609351350478231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8175106178145801800637641 6131329633609351350478231)
              ·
                refine ⟨9196994450414027025717347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6131329633609351350478231 9196994450414027025717347)
                ·
                  refine ⟨13795491675621040538576021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9196994450414027025717347 13795491675621040538576021)
                  ·
                    refine ⟨646663672294736275245751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13795491675621040538576021 646663672294736275245751)
                    ·
                      rfl

theorem cell23_3778119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_3778119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3778119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3778119 prefixEnd_3778119 := by exact prefixLift 3778119
  have htrace : WordTrace (prefixWord ++ tailWord_3778119) baseStart_3778119 baseEnd_3778119 := by
    simpa [prefixWord, tailWord_3778119, baseEnd_3778119] using wordTrace_append hprefix tailTrace_3778119
  have hstable : (prefixWord ++ tailWord_3778119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778119).length < 2 ^ (prefixWord ++ tailWord_3778119).sum := by decide
  have hdescent : baseEnd_3778119 < baseStart_3778119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778129 : List Nat := [1, 2, 2, 1, 3, 2, 2, 4, 1, 2, 3]
def baseStart_3778129 : Nat := 118140960795 + 3778129 * 2 ^ 59
def prefixEnd_3778129 : Nat := 4983230072969 + 3 ^ 40 * 3778129 * 2
def baseEnd_3778129 : Nat := 1939996151690753786612207

theorem tailTrace_3778129 : CollatzResearch.WordTrace tailWord_3778129 prefixEnd_3778129 1939996151690753786612207 := by
  unfold tailWord_3778129
  simp only [CollatzResearch.WordTrace]
  refine ⟨137799685329491360907089441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91866456886327573938059627 137799685329491360907089441)
  ·
    refine ⟨103349763997118520680317081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137799685329491360907089441 103349763997118520680317081)
    ·
      refine ⟨77512322997838890510237811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103349763997118520680317081 77512322997838890510237811)
      ·
        refine ⟨116268484496758335765356717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77512322997838890510237811 116268484496758335765356717)
        ·
          refine ⟨43600681686284375912008769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116268484496758335765356717 43600681686284375912008769)
          ·
            refine ⟨32700511264713281934006577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43600681686284375912008769 32700511264713281934006577)
            ·
              refine ⟨24525383448534961450504933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32700511264713281934006577 24525383448534961450504933)
              ·
                refine ⟨4598509396600305271969675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24525383448534961450504933 4598509396600305271969675)
                ·
                  refine ⟨6897764094900457907954513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4598509396600305271969675 6897764094900457907954513)
                  ·
                    refine ⟨5173323071175343430965885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6897764094900457907954513 5173323071175343430965885)
                    ·
                      refine ⟨1939996151690753786612207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5173323071175343430965885 1939996151690753786612207)
                      ·
                        rfl

theorem cell23_3778129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 2, 3].length) (baseStart_3778129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3778129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3778129 prefixEnd_3778129 := by exact prefixLift 3778129
  have htrace : WordTrace (prefixWord ++ tailWord_3778129) baseStart_3778129 baseEnd_3778129 := by
    simpa [prefixWord, tailWord_3778129, baseEnd_3778129] using wordTrace_append hprefix tailTrace_3778129
  have hstable : (prefixWord ++ tailWord_3778129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778129).length < 2 ^ (prefixWord ++ tailWord_3778129).sum := by decide
  have hdescent : baseEnd_3778129 < baseStart_3778129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778194 : List Nat := [3, 2, 3, 1, 4, 1, 1, 3, 1, 2, 2]
def baseStart_3778194 : Nat := 118140960795 + 3778194 * 2 ^ 59
def prefixEnd_3778194 : Nat := 4983230072969 + 3 ^ 40 * 3778194 * 2
def baseEnd_3778194 : Nat := 1940029527933296032299409

theorem tailTrace_3778194 : CollatzResearch.WordTrace tailWord_3778194 prefixEnd_3778194 1940029527933296032299409 := by
  unfold tailWord_3778194
  simp only [CollatzResearch.WordTrace]
  refine ⟨34450514018563969252051409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91868037382837251338803757 34450514018563969252051409)
  ·
    refine ⟨25837885513922976939038557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34450514018563969252051409 25837885513922976939038557)
    ·
      refine ⟨9689207067721116352139459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25837885513922976939038557 9689207067721116352139459)
      ·
        refine ⟨14533810601581674528209189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9689207067721116352139459 14533810601581674528209189)
        ·
          refine ⟨2725089487796563974039223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14533810601581674528209189 2725089487796563974039223)
          ·
            refine ⟨4087634231694845961058835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2725089487796563974039223 4087634231694845961058835)
            ·
              refine ⟨6131451347542268941588253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4087634231694845961058835 6131451347542268941588253)
              ·
                refine ⟨2299294255328350853095595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6131451347542268941588253 2299294255328350853095595)
                ·
                  refine ⟨3448941382992526279643393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2299294255328350853095595 3448941382992526279643393)
                  ·
                    refine ⟨2586706037244394709732545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3448941382992526279643393 2586706037244394709732545)
                    ·
                      refine ⟨1940029527933296032299409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2586706037244394709732545 1940029527933296032299409)
                      ·
                        rfl

theorem cell23_3778194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_3778194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3778194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3778194 prefixEnd_3778194 := by exact prefixLift 3778194
  have htrace : WordTrace (prefixWord ++ tailWord_3778194) baseStart_3778194 baseEnd_3778194 := by
    simpa [prefixWord, tailWord_3778194, baseEnd_3778194] using wordTrace_append hprefix tailTrace_3778194
  have hstable : (prefixWord ++ tailWord_3778194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778194).length < 2 ^ (prefixWord ++ tailWord_3778194).sum := by decide
  have hdescent : baseEnd_3778194 < baseStart_3778194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778306 : List Nat := [3, 4, 1, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_3778306 : Nat := 118140960795 + 3778306 * 2 ^ 59
def prefixEnd_3778306 : Nat := 4983230072969 + 3 ^ 40 * 3778306 * 2
def baseEnd_3778306 : Nat := 1940087037766599594098893

theorem tailTrace_3778306 : CollatzResearch.WordTrace tailWord_3778306 prefixEnd_3778306 1940087037766599594098893 := by
  unfold tailWord_3778306
  simp only [CollatzResearch.WordTrace]
  refine ⟨34451535262462530034070693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91870760699900080090855181 34451535262462530034070693)
  ·
    refine ⟨6459662861711724381388255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34451535262462530034070693 6459662861711724381388255)
    ·
      refine ⟨9689494292567586572082383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6459662861711724381388255 9689494292567586572082383)
      ·
        refine ⟨14534241438851379858123575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9689494292567586572082383 14534241438851379858123575)
        ·
          refine ⟨21801362158277069787185363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14534241438851379858123575 21801362158277069787185363)
          ·
            refine ⟨32702043237415604680778045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21801362158277069787185363 32702043237415604680778045)
            ·
              refine ⟨12263266214030851755291767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32702043237415604680778045 12263266214030851755291767)
              ·
                refine ⟨18394899321046277632937651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12263266214030851755291767 18394899321046277632937651)
                ·
                  refine ⟨27592348981569416449406477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18394899321046277632937651 27592348981569416449406477)
                  ·
                    refine ⟨10347130868088531168527429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27592348981569416449406477 10347130868088531168527429)
                    ·
                      refine ⟨1940087037766599594098893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10347130868088531168527429 1940087037766599594098893)
                      ·
                        rfl

theorem cell23_3778306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_3778306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3778306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3778306 prefixEnd_3778306 := by exact prefixLift 3778306
  have htrace : WordTrace (prefixWord ++ tailWord_3778306) baseStart_3778306 baseEnd_3778306 := by
    simpa [prefixWord, tailWord_3778306, baseEnd_3778306] using wordTrace_append hprefix tailTrace_3778306
  have hstable : (prefixWord ++ tailWord_3778306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778306).length < 2 ^ (prefixWord ++ tailWord_3778306).sum := by decide
  have hdescent : baseEnd_3778306 < baseStart_3778306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778367 : List Nat := [1, 1, 2, 2, 7, 1, 1, 3, 1, 4]
def baseStart_3778367 : Nat := 118140960795 + 3778367 * 2 ^ 59
def prefixEnd_3778367 : Nat := 4983230072969 + 3 ^ 40 * 3778367 * 2
def baseEnd_3778367 : Nat := 646706120028841285145371

theorem tailTrace_3778367 : CollatzResearch.WordTrace tailWord_3778367 prefixEnd_3778367 646706120028841285145371 := by
  unfold tailWord_3778367
  simp only [CollatzResearch.WordTrace]
  refine ⟨137808365902629127554253355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91872243935086085036168903 137808365902629127554253355)
  ·
    refine ⟨206712548853943691331380033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137808365902629127554253355 206712548853943691331380033)
    ·
      refine ⟨155034411640457768498535025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206712548853943691331380033 155034411640457768498535025)
      ·
        refine ⟨116275808730343326373901269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155034411640457768498535025 116275808730343326373901269)
        ·
          refine ⟨2725214267117421711888311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 116275808730343326373901269 2725214267117421711888311)
          ·
            refine ⟨4087821400676132567832467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2725214267117421711888311 4087821400676132567832467)
            ·
              refine ⟨6131732101014198851748701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4087821400676132567832467 6131732101014198851748701)
              ·
                refine ⟨2299399537880324569405763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6131732101014198851748701 2299399537880324569405763)
                ·
                  refine ⟨3449099306820486854108645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2299399537880324569405763 3449099306820486854108645)
                  ·
                    refine ⟨646706120028841285145371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3449099306820486854108645 646706120028841285145371)
                    ·
                      rfl

theorem cell23_3778367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 3, 1, 4].length) (baseStart_3778367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3778367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3778367 prefixEnd_3778367 := by exact prefixLift 3778367
  have htrace : WordTrace (prefixWord ++ tailWord_3778367) baseStart_3778367 baseEnd_3778367 := by
    simpa [prefixWord, tailWord_3778367, baseEnd_3778367] using wordTrace_append hprefix tailTrace_3778367
  have hstable : (prefixWord ++ tailWord_3778367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778367).length < 2 ^ (prefixWord ++ tailWord_3778367).sum := by decide
  have hdescent : baseEnd_3778367 < baseStart_3778367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778376 : List Nat := [2, 1, 3, 1, 1, 4, 2, 3, 1, 5]
def baseStart_3778376 : Nat := 118140960795 + 3778376 * 2 ^ 59
def prefixEnd_3778376 : Nat := 4983230072969 + 3 ^ 40 * 3778376 * 2
def baseEnd_3778376 : Nat := 646707660470804773407857

theorem tailTrace_3778376 : CollatzResearch.WordTrace tailWord_3778376 prefixEnd_3778376 646707660470804773407857 := by
  unfold tailWord_3778376
  simp only [CollatzResearch.WordTrace]
  refine ⟨68904347079798261045665491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91872462773064348060887321 68904347079798261045665491)
  ·
    refine ⟨103356520619697391568498237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68904347079798261045665491 103356520619697391568498237)
    ·
      refine ⟨38758695232386521838186839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103356520619697391568498237 38758695232386521838186839)
      ·
        refine ⟨58138042848579782757280259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38758695232386521838186839 58138042848579782757280259)
        ·
          refine ⟨87207064272869674135920389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58138042848579782757280259 87207064272869674135920389)
          ·
            refine ⟨16351324551163063900485073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87207064272869674135920389 16351324551163063900485073)
            ·
              refine ⟨12263493413372297925363805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16351324551163063900485073 12263493413372297925363805)
              ·
                refine ⟨4598810030014611722011427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12263493413372297925363805 4598810030014611722011427)
                ·
                  refine ⟨6898215045021917583017141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4598810030014611722011427 6898215045021917583017141)
                  ·
                    refine ⟨646707660470804773407857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6898215045021917583017141 646707660470804773407857)
                    ·
                      rfl

theorem cell23_3778376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_3778376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3778376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3778376 prefixEnd_3778376 := by exact prefixLift 3778376
  have htrace : WordTrace (prefixWord ++ tailWord_3778376) baseStart_3778376 baseEnd_3778376 := by
    simpa [prefixWord, tailWord_3778376, baseEnd_3778376] using wordTrace_append hprefix tailTrace_3778376
  have hstable : (prefixWord ++ tailWord_3778376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778376).length < 2 ^ (prefixWord ++ tailWord_3778376).sum := by decide
  have hdescent : baseEnd_3778376 < baseStart_3778376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778409 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 5, 2, 4]
def baseStart_3778409 : Nat := 118140960795 + 3778409 * 2 ^ 59
def prefixEnd_3778409 : Nat := 4983230072969 + 3 ^ 40 * 3778409 * 2
def baseEnd_3778409 : Nat := 1940139926274012691110919

theorem tailTrace_3778409 : CollatzResearch.WordTrace tailWord_3778409 prefixEnd_3778409 1940139926274012691110919 := by
  unfold tailWord_3778409
  simp only [CollatzResearch.WordTrace]
  refine ⟨137809897768476968727282281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91873265178984645818188187 137809897768476968727282281)
  ·
    refine ⟨103357423326357726545461711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137809897768476968727282281 103357423326357726545461711)
    ·
      refine ⟨155036134989536589818192567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103357423326357726545461711 155036134989536589818192567)
      ·
        refine ⟨232554202484304884727288851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155036134989536589818192567 232554202484304884727288851)
        ·
          refine ⟨348831303726457327090933277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232554202484304884727288851 348831303726457327090933277)
          ·
            refine ⟨130811738897421497659099979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 348831303726457327090933277 130811738897421497659099979)
            ·
              refine ⟨196217608346132246488649969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130811738897421497659099979 196217608346132246488649969)
              ·
                refine ⟨147163206259599184866487477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196217608346132246488649969 147163206259599184866487477)
                ·
                  refine ⟨13796550586837423581233201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 147163206259599184866487477 13796550586837423581233201)
                  ·
                    refine ⟨10347412940128067685924901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13796550586837423581233201 10347412940128067685924901)
                    ·
                      refine ⟨1940139926274012691110919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10347412940128067685924901 1940139926274012691110919)
                      ·
                        rfl

theorem cell23_3778409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 2, 4].length) (baseStart_3778409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3778409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3778409 prefixEnd_3778409 := by exact prefixLift 3778409
  have htrace : WordTrace (prefixWord ++ tailWord_3778409) baseStart_3778409 baseEnd_3778409 := by
    simpa [prefixWord, tailWord_3778409, baseEnd_3778409] using wordTrace_append hprefix tailTrace_3778409
  have hstable : (prefixWord ++ tailWord_3778409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778409).length < 2 ^ (prefixWord ++ tailWord_3778409).sum := by decide
  have hdescent : baseEnd_3778409 < baseStart_3778409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778413 : List Nat := [1, 5, 1, 1, 1, 1, 5, 2, 1, 1, 4]
def baseStart_3778413 : Nat := 118140960795 + 3778413 * 2 ^ 59
def prefixEnd_3778413 : Nat := 4983230072969 + 3 ^ 40 * 3778413 * 2
def baseEnd_3778413 : Nat := 1940141980196630675460901

theorem tailTrace_3778413 : CollatzResearch.WordTrace tailWord_3778413 prefixEnd_3778413 1940141980196630675460901 := by
  unfold tailWord_3778413
  simp only [CollatzResearch.WordTrace]
  refine ⟨137810043660462477410427893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91873362440308318273618595 137810043660462477410427893)
  ·
    refine ⟨12919691593168357257227615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137810043660462477410427893 12919691593168357257227615)
    ·
      refine ⟨19379537389752535885841423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12919691593168357257227615 19379537389752535885841423)
      ·
        refine ⟨29069306084628803828762135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19379537389752535885841423 29069306084628803828762135)
        ·
          refine ⟨43603959126943205743143203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29069306084628803828762135 43603959126943205743143203)
          ·
            refine ⟨65405938690414808614714805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43603959126943205743143203 65405938690414808614714805)
            ·
              refine ⟨6131806752226388307629513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65405938690414808614714805 6131806752226388307629513)
              ·
                refine ⟨4598855064169791230722135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6131806752226388307629513 4598855064169791230722135)
                ·
                  refine ⟨6898282596254686846083203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4598855064169791230722135 6898282596254686846083203)
                  ·
                    refine ⟨10347423894382030269124805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6898282596254686846083203 10347423894382030269124805)
                    ·
                      refine ⟨1940141980196630675460901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10347423894382030269124805 1940141980196630675460901)
                      ·
                        rfl

theorem cell23_3778413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_3778413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3778413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3778413 prefixEnd_3778413 := by exact prefixLift 3778413
  have htrace : WordTrace (prefixWord ++ tailWord_3778413) baseStart_3778413 baseEnd_3778413 := by
    simpa [prefixWord, tailWord_3778413, baseEnd_3778413] using wordTrace_append hprefix tailTrace_3778413
  have hstable : (prefixWord ++ tailWord_3778413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778413).length < 2 ^ (prefixWord ++ tailWord_3778413).sum := by decide
  have hdescent : baseEnd_3778413 < baseStart_3778413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778440 : List Nat := [2, 1, 3, 3, 3, 1, 2, 2, 2, 4]
def baseStart_3778440 : Nat := 118140960795 + 3778440 * 2 ^ 59
def prefixEnd_3778440 : Nat := 4983230072969 + 3 ^ 40 * 3778440 * 2
def baseEnd_3778440 : Nat := 646718614724767356607759

theorem tailTrace_3778440 : CollatzResearch.WordTrace tailWord_3778440 prefixEnd_3778440 646718614724767356607759 := by
  unfold tailWord_3778440
  simp only [CollatzResearch.WordTrace]
  refine ⟨68905514215682330510830387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91874018954243107347773849 68905514215682330510830387)
  ·
    refine ⟨103358271323523495766245581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68905514215682330510830387 103358271323523495766245581)
    ·
      refine ⟨38759351746321310912342093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103358271323523495766245581 38759351746321310912342093)
      ·
        refine ⟨14534756904870491592128285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38759351746321310912342093 14534756904870491592128285)
        ·
          refine ⟨5450533839326434347048107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14534756904870491592128285 5450533839326434347048107)
          ·
            refine ⟨8175800758989651520572161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5450533839326434347048107 8175800758989651520572161)
            ·
              refine ⟨6131850569242238640429121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8175800758989651520572161 6131850569242238640429121)
              ·
                refine ⟨4598887926931678980321841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6131850569242238640429121 4598887926931678980321841)
                ·
                  refine ⟨3449165945198759235241381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4598887926931678980321841 3449165945198759235241381)
                  ·
                    refine ⟨646718614724767356607759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3449165945198759235241381 646718614724767356607759)
                    ·
                      rfl

theorem cell23_3778440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_3778440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3778440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3778440 prefixEnd_3778440 := by exact prefixLift 3778440
  have htrace : WordTrace (prefixWord ++ tailWord_3778440) baseStart_3778440 baseEnd_3778440 := by
    simpa [prefixWord, tailWord_3778440, baseEnd_3778440] using wordTrace_append hprefix tailTrace_3778440
  have hstable : (prefixWord ++ tailWord_3778440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778440).length < 2 ^ (prefixWord ++ tailWord_3778440).sum := by decide
  have hdescent : baseEnd_3778440 < baseStart_3778440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778449 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 2, 7]
def baseStart_3778449 : Nat := 118140960795 + 3778449 * 2 ^ 59
def prefixEnd_3778449 : Nat := 4983230072969 + 3 ^ 40 * 3778449 * 2
def baseEnd_3778449 : Nat := 646720155166730844870245

theorem tailTrace_3778449 : CollatzResearch.WordTrace tailWord_3778449 prefixEnd_3778449 646720155166730844870245 := by
  unfold tailWord_3778449
  simp only [CollatzResearch.WordTrace]
  refine ⟨137811356688332055558738401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91874237792221370372492267 137811356688332055558738401)
  ·
    refine ⟨103358517516249041669053801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137811356688332055558738401 103358517516249041669053801)
    ·
      refine ⟨77518888137186781251790351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103358517516249041669053801 77518888137186781251790351)
      ·
        refine ⟨116278332205780171877685527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77518888137186781251790351 116278332205780171877685527)
        ·
          refine ⟨174417498308670257816528291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116278332205780171877685527 174417498308670257816528291)
          ·
            refine ⟨261626247463005386724792437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174417498308670257816528291 261626247463005386724792437)
            ·
              refine ⟨24527460699656755005449291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 261626247463005386724792437 24527460699656755005449291)
              ·
                refine ⟨36791191049485132508173937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24527460699656755005449291 36791191049485132508173937)
                ·
                  refine ⟨27593393287113849381130453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36791191049485132508173937 27593393287113849381130453)
                  ·
                    refine ⟨646720155166730844870245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27593393287113849381130453 646720155166730844870245)
                    ·
                      rfl

theorem cell23_3778449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 7].length) (baseStart_3778449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3778449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3778449 prefixEnd_3778449 := by exact prefixLift 3778449
  have htrace : WordTrace (prefixWord ++ tailWord_3778449) baseStart_3778449 baseEnd_3778449 := by
    simpa [prefixWord, tailWord_3778449, baseEnd_3778449] using wordTrace_append hprefix tailTrace_3778449
  have hstable : (prefixWord ++ tailWord_3778449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778449).length < 2 ^ (prefixWord ++ tailWord_3778449).sum := by decide
  have hdescent : baseEnd_3778449 < baseStart_3778449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778479 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 1, 8]
def baseStart_3778479 : Nat := 118140960795 + 3778479 * 2 ^ 59
def prefixEnd_3778479 : Nat := 4983230072969 + 3 ^ 40 * 3778479 * 2
def baseEnd_3778479 : Nat := 646725289973275805745199

theorem tailTrace_3778479 : CollatzResearch.WordTrace tailWord_3778479 prefixEnd_3778479 646725289973275805745199 := by
  unfold tailWord_3778479
  simp only [CollatzResearch.WordTrace]
  refine ⟨137812450878223370682330491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91874967252148913788220327 137812450878223370682330491)
  ·
    refine ⟨206718676317335056023495737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137812450878223370682330491 206718676317335056023495737)
    ·
      refine ⟨155039007238001292017621803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206718676317335056023495737 155039007238001292017621803)
      ·
        refine ⟨232558510857001938026432705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155039007238001292017621803 232558510857001938026432705)
        ·
          refine ⟨174418883142751453519824529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232558510857001938026432705 174418883142751453519824529)
          ·
            refine ⟨130814162357063590139868397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174418883142751453519824529 130814162357063590139868397)
            ·
              refine ⟨49055310883898846302450649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130814162357063590139868397 49055310883898846302450649)
              ·
                refine ⟨36791483162924134726837987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49055310883898846302450649 36791483162924134726837987)
                ·
                  refine ⟨55187224744386202090256981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36791483162924134726837987 55187224744386202090256981)
                  ·
                    refine ⟨646725289973275805745199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55187224744386202090256981 646725289973275805745199)
                    ·
                      rfl

theorem cell23_3778479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 8].length) (baseStart_3778479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3778479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3778479 prefixEnd_3778479 := by exact prefixLift 3778479
  have htrace : WordTrace (prefixWord ++ tailWord_3778479) baseStart_3778479 baseEnd_3778479 := by
    simpa [prefixWord, tailWord_3778479, baseEnd_3778479] using wordTrace_append hprefix tailTrace_3778479
  have hstable : (prefixWord ++ tailWord_3778479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778479).length < 2 ^ (prefixWord ++ tailWord_3778479).sum := by decide
  have hdescent : baseEnd_3778479 < baseStart_3778479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778499 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 6]
def baseStart_3778499 : Nat := 118140960795 + 3778499 * 2 ^ 59
def prefixEnd_3778499 : Nat := 4983230072969 + 3 ^ 40 * 3778499 * 2
def baseEnd_3778499 : Nat := 1940186139532917338985505

theorem tailTrace_3778499 : CollatzResearch.WordTrace tailWord_3778499 prefixEnd_3778499 1940186139532917338985505 := by
  unfold tailWord_3778499
  simp only [CollatzResearch.WordTrace]
  refine ⟨137813180338150914098058551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91875453558767276065372367 137813180338150914098058551)
  ·
    refine ⟨206719770507226371147087827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137813180338150914098058551 206719770507226371147087827)
    ·
      refine ⟨310079655760839556720631741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206719770507226371147087827 310079655760839556720631741)
      ·
        refine ⟨116279870910314833770236903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 310079655760839556720631741 116279870910314833770236903)
        ·
          refine ⟨174419806365472250655355355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116279870910314833770236903 174419806365472250655355355)
          ·
            refine ⟨261629709548208375983033033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174419806365472250655355355 261629709548208375983033033)
            ·
              refine ⟨196222282161156281987274775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261629709548208375983033033 196222282161156281987274775)
              ·
                refine ⟨294333423241734422980912163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196222282161156281987274775 294333423241734422980912163)
                ·
                  refine ⟨441500134862601634471368245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 294333423241734422980912163 441500134862601634471368245)
                  ·
                    refine ⟨41390637643368903231690773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 441500134862601634471368245 41390637643368903231690773)
                    ·
                      refine ⟨1940186139532917338985505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41390637643368903231690773 1940186139532917338985505)
                      ·
                        rfl

theorem cell23_3778499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_3778499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3778499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3778499 prefixEnd_3778499 := by exact prefixLift 3778499
  have htrace : WordTrace (prefixWord ++ tailWord_3778499) baseStart_3778499 baseEnd_3778499 := by
    simpa [prefixWord, tailWord_3778499, baseEnd_3778499] using wordTrace_append hprefix tailTrace_3778499
  have hstable : (prefixWord ++ tailWord_3778499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778499).length < 2 ^ (prefixWord ++ tailWord_3778499).sum := by decide
  have hdescent : baseEnd_3778499 < baseStart_3778499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778506 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 1, 6, 3]
def baseStart_3778506 : Nat := 118140960795 + 3778506 * 2 ^ 59
def prefixEnd_3778506 : Nat := 4983230072969 + 3 ^ 40 * 3778506 * 2
def baseEnd_3778506 : Nat := 1940189733897498811597973

theorem tailTrace_3778506 : CollatzResearch.WordTrace tailWord_3778506 prefixEnd_3778506 1940189733897498811597973 := by
  unfold tailWord_3778506
  simp only [CollatzResearch.WordTrace]
  refine ⟨34453358912281388573390843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91875623766083702862375581 34453358912281388573390843)
  ·
    refine ⟨51680038368422082860086265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34453358912281388573390843 51680038368422082860086265)
    ·
      refine ⟨38760028776316562145064699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51680038368422082860086265 38760028776316562145064699)
      ·
        refine ⟨58140043164474843217597049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38760028776316562145064699 58140043164474843217597049)
        ·
          refine ⟨43605032373356132413197787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58140043164474843217597049 43605032373356132413197787)
          ·
            refine ⟨65407548560034198619796681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43605032373356132413197787 65407548560034198619796681)
            ·
              refine ⟨49055661420025648964847511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65407548560034198619796681 49055661420025648964847511)
              ·
                refine ⟨73583492130038473447271267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49055661420025648964847511 73583492130038473447271267)
                ·
                  refine ⟨110375238195057710170906901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73583492130038473447271267 110375238195057710170906901)
                  ·
                    refine ⟨5173839290393330164261261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110375238195057710170906901 5173839290393330164261261)
                    ·
                      refine ⟨1940189733897498811597973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5173839290393330164261261 1940189733897498811597973)
                      ·
                        rfl

theorem cell23_3778506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_3778506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3778506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3778506 prefixEnd_3778506 := by exact prefixLift 3778506
  have htrace : WordTrace (prefixWord ++ tailWord_3778506) baseStart_3778506 baseEnd_3778506 := by
    simpa [prefixWord, tailWord_3778506, baseEnd_3778506] using wordTrace_append hprefix tailTrace_3778506
  have hstable : (prefixWord ++ tailWord_3778506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778506).length < 2 ^ (prefixWord ++ tailWord_3778506).sum := by decide
  have hdescent : baseEnd_3778506 < baseStart_3778506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778514 : List Nat := [3, 2, 2, 3, 2, 1, 3, 1, 2, 1, 3]
def baseStart_3778514 : Nat := 118140960795 + 3778514 * 2 ^ 59
def prefixEnd_3778514 : Nat := 4983230072969 + 3 ^ 40 * 3778514 * 2
def baseEnd_3778514 : Nat := 1940193841742734780297937

theorem tailTrace_3778514 : CollatzResearch.WordTrace tailWord_3778514 prefixEnd_3778514 1940193841742734780297937 := by
  unfold tailWord_3778514
  simp only [CollatzResearch.WordTrace]
  refine ⟨34453431858274142914963649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91875818288731047773236397 34453431858274142914963649)
  ·
    refine ⟨25840073893705607186222737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34453431858274142914963649 25840073893705607186222737)
    ·
      refine ⟨19380055420279205389667053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25840073893705607186222737 19380055420279205389667053)
      ·
        refine ⟨7267520782604702021125145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19380055420279205389667053 7267520782604702021125145)
        ·
          refine ⟨5450640586953526515843859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7267520782604702021125145 5450640586953526515843859)
          ·
            refine ⟨8175960880430289773765789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5450640586953526515843859 8175960880430289773765789)
            ·
              refine ⟨3065985330161358665162171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8175960880430289773765789 3065985330161358665162171)
              ·
                refine ⟨4598977995242037997743257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3065985330161358665162171 4598977995242037997743257)
                ·
                  refine ⟨3449233496431528498307443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4598977995242037997743257 3449233496431528498307443)
                  ·
                    refine ⟨5173850244647292747461165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3449233496431528498307443 5173850244647292747461165)
                    ·
                      refine ⟨1940193841742734780297937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5173850244647292747461165 1940193841742734780297937)
                      ·
                        rfl

theorem cell23_3778514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_3778514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3778514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3778514 prefixEnd_3778514 := by exact prefixLift 3778514
  have htrace : WordTrace (prefixWord ++ tailWord_3778514) baseStart_3778514 baseEnd_3778514 := by
    simpa [prefixWord, tailWord_3778514, baseEnd_3778514] using wordTrace_append hprefix tailTrace_3778514
  have hstable : (prefixWord ++ tailWord_3778514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778514).length < 2 ^ (prefixWord ++ tailWord_3778514).sum := by decide
  have hdescent : baseEnd_3778514 < baseStart_3778514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778711 : List Nat := [1, 1, 3, 3, 4, 2, 1, 3, 1, 1, 3]
def baseStart_3778711 : Nat := 118140960795 + 3778711 * 2 ^ 59
def prefixEnd_3778711 : Nat := 4983230072969 + 3 ^ 40 * 3778711 * 2
def baseEnd_3778711 : Nat := 1940294997431670509534531

theorem tailTrace_3778711 : CollatzResearch.WordTrace tailWord_3778711 prefixEnd_3778711 1940294997431670509534531 := by
  unfold tailWord_3778711
  simp only [CollatzResearch.WordTrace]
  refine ⟨137820912613382874304775987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91880608408921916203183991 137820912613382874304775987)
  ·
    refine ⟨206731368920074311457163981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137820912613382874304775987 206731368920074311457163981)
    ·
      refine ⟨77524263345027866796436493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206731368920074311457163981 77524263345027866796436493)
      ·
        refine ⟨29071598754385450048663685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77524263345027866796436493 29071598754385450048663685)
        ·
          refine ⟨5450924766447271884124441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29071598754385450048663685 5450924766447271884124441)
          ·
            refine ⟨4088193574835453913093331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5450924766447271884124441 4088193574835453913093331)
            ·
              refine ⟨6132290362253180869639997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4088193574835453913093331 6132290362253180869639997)
              ·
                refine ⟨2299608885844942826114999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6132290362253180869639997 2299608885844942826114999)
                ·
                  refine ⟨3449413328767414239172499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2299608885844942826114999 3449413328767414239172499)
                  ·
                    refine ⟨5174119993151121358758749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3449413328767414239172499 5174119993151121358758749)
                    ·
                      refine ⟨1940294997431670509534531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5174119993151121358758749 1940294997431670509534531)
                      ·
                        rfl

theorem cell23_3778711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_3778711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3778711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3778711 prefixEnd_3778711 := by exact prefixLift 3778711
  have htrace : WordTrace (prefixWord ++ tailWord_3778711) baseStart_3778711 baseEnd_3778711 := by
    simpa [prefixWord, tailWord_3778711, baseEnd_3778711] using wordTrace_append hprefix tailTrace_3778711
  have hstable : (prefixWord ++ tailWord_3778711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778711).length < 2 ^ (prefixWord ++ tailWord_3778711).sum := by decide
  have hdescent : baseEnd_3778711 < baseStart_3778711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778713 : List Nat := [1, 2, 1, 2, 1, 2, 1, 6, 1, 2, 4]
def baseStart_3778713 : Nat := 118140960795 + 3778713 * 2 ^ 59
def prefixEnd_3778713 : Nat := 4983230072969 + 3 ^ 40 * 3778713 * 2
def baseEnd_3778713 : Nat := 1940296024392979501709521

theorem tailTrace_3778713 : CollatzResearch.WordTrace tailWord_3778713 prefixEnd_3778713 1940296024392979501709521 := by
  unfold tailWord_3778713
  simp only [CollatzResearch.WordTrace]
  refine ⟨137820985559375628646348793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91880657039583752430899195 137820985559375628646348793)
  ·
    refine ⟨103365739169531721484761595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137820985559375628646348793 103365739169531721484761595)
    ·
      refine ⟨155048608754297582227142393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103365739169531721484761595 155048608754297582227142393)
      ·
        refine ⟨116286456565723186670356795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155048608754297582227142393 116286456565723186670356795)
        ·
          refine ⟨174429684848584780005535193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116286456565723186670356795 174429684848584780005535193)
          ·
            refine ⟨130822263636438585004151395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174429684848584780005535193 130822263636438585004151395)
            ·
              refine ⟨196233395454657877506227093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130822263636438585004151395 196233395454657877506227093)
              ·
                refine ⟨9198440411937088008104395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 196233395454657877506227093 9198440411937088008104395)
                ·
                  refine ⟨13797660617905632012156593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9198440411937088008104395 13797660617905632012156593)
                  ·
                    refine ⟨10348245463429224009117445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13797660617905632012156593 10348245463429224009117445)
                    ·
                      refine ⟨1940296024392979501709521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10348245463429224009117445 1940296024392979501709521)
                      ·
                        rfl

theorem cell23_3778713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 2, 4].length) (baseStart_3778713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3778713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3778713 prefixEnd_3778713 := by exact prefixLift 3778713
  have htrace : WordTrace (prefixWord ++ tailWord_3778713) baseStart_3778713 baseEnd_3778713 := by
    simpa [prefixWord, tailWord_3778713, baseEnd_3778713] using wordTrace_append hprefix tailTrace_3778713
  have hstable : (prefixWord ++ tailWord_3778713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778713).length < 2 ^ (prefixWord ++ tailWord_3778713).sum := by decide
  have hdescent : baseEnd_3778713 < baseStart_3778713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778720 : List Nat := [2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 5]
def baseStart_3778720 : Nat := 118140960795 + 3778720 * 2 ^ 59
def prefixEnd_3778720 : Nat := 4983230072969 + 3 ^ 40 * 3778720 * 2
def baseEnd_3778720 : Nat := 1940299618757560974321989

theorem tailTrace_3778720 : CollatzResearch.WordTrace tailWord_3778720 prefixEnd_3778720 1940299618757560974321989 := by
  unfold tailWord_3778720
  simp only [CollatzResearch.WordTrace]
  refine ⟨68910620435175134420926807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91880827246900179227902409 68910620435175134420926807)
  ·
    refine ⟨103365930652762701631390211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68910620435175134420926807 103365930652762701631390211)
    ·
      refine ⟨155048895979144052447085317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103365930652762701631390211 155048895979144052447085317)
      ·
        refine ⟨29071667996089509833828497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155048895979144052447085317 29071667996089509833828497)
        ·
          refine ⟨21803750997067132375371373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29071667996089509833828497 21803750997067132375371373)
          ·
            refine ⟨8176406623900174640764265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21803750997067132375371373 8176406623900174640764265)
            ·
              refine ⟨6132304967925130980573199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8176406623900174640764265 6132304967925130980573199)
              ·
                refine ⟨9198457451887696470859799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6132304967925130980573199 9198457451887696470859799)
                ·
                  refine ⟨13797686177831544706289699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9198457451887696470859799 13797686177831544706289699)
                  ·
                    refine ⟨20696529266747317059434549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13797686177831544706289699 20696529266747317059434549)
                    ·
                      refine ⟨1940299618757560974321989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20696529266747317059434549 1940299618757560974321989)
                      ·
                        rfl

theorem cell23_3778720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_3778720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3778720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3778720 prefixEnd_3778720 := by exact prefixLift 3778720
  have htrace : WordTrace (prefixWord ++ tailWord_3778720) baseStart_3778720 baseEnd_3778720 := by
    simpa [prefixWord, tailWord_3778720, baseEnd_3778720] using wordTrace_append hprefix tailTrace_3778720
  have hstable : (prefixWord ++ tailWord_3778720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778720).length < 2 ^ (prefixWord ++ tailWord_3778720).sum := by decide
  have hdescent : baseEnd_3778720 < baseStart_3778720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778777 : List Nat := [1, 2, 1, 2, 3, 1, 2, 5, 1, 3, 2]
def baseStart_3778777 : Nat := 118140960795 + 3778777 * 2 ^ 59
def prefixEnd_3778777 : Nat := 4983230072969 + 3 ^ 40 * 3778777 * 2
def baseEnd_3778777 : Nat := 1940328887154867251309227

theorem tailTrace_3778777 : CollatzResearch.WordTrace tailWord_3778777 prefixEnd_3778777 1940328887154867251309227 := by
  unfold tailWord_3778777
  simp only [CollatzResearch.WordTrace]
  refine ⟨137823319831143767576678585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91882213220762511717785723 137823319831143767576678585)
  ·
    refine ⟨103367489873357825682508939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137823319831143767576678585 103367489873357825682508939)
    ·
      refine ⟨155051234810036738523763409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103367489873357825682508939 155051234810036738523763409)
      ·
        refine ⟨116288426107527553892822557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155051234810036738523763409 116288426107527553892822557)
        ·
          refine ⟨43608159790322832709808459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116288426107527553892822557 43608159790322832709808459)
          ·
            refine ⟨65412239685484249064712689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43608159790322832709808459 65412239685484249064712689)
            ·
              refine ⟨49059179764113186798534517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65412239685484249064712689 49059179764113186798534517)
              ·
                refine ⟨4599298102885611262362611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49059179764113186798534517 4599298102885611262362611)
                ·
                  refine ⟨6898947154328416893543917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4599298102885611262362611 6898947154328416893543917)
                  ·
                    refine ⟨2587105182873156335078969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6898947154328416893543917 2587105182873156335078969)
                    ·
                      refine ⟨1940328887154867251309227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2587105182873156335078969 1940328887154867251309227)
                      ·
                        rfl

theorem cell23_3778777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 3, 2].length) (baseStart_3778777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3778777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3778777 prefixEnd_3778777 := by exact prefixLift 3778777
  have htrace : WordTrace (prefixWord ++ tailWord_3778777) baseStart_3778777 baseEnd_3778777 := by
    simpa [prefixWord, tailWord_3778777, baseEnd_3778777] using wordTrace_append hprefix tailTrace_3778777
  have hstable : (prefixWord ++ tailWord_3778777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778777).length < 2 ^ (prefixWord ++ tailWord_3778777).sum := by decide
  have hdescent : baseEnd_3778777 < baseStart_3778777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778783 : List Nat := [1, 1, 2, 3, 2, 1, 1, 4, 2, 6]
def baseStart_3778783 : Nat := 118140960795 + 3778783 * 2 ^ 59
def prefixEnd_3778783 : Nat := 4983230072969 + 3 ^ 40 * 3778783 * 2
def baseEnd_3778783 : Nat := 646777322679598075944733

theorem tailTrace_3778783 : CollatzResearch.WordTrace tailWord_3778783 prefixEnd_3778783 646777322679598075944733 := by
  unfold tailWord_3778783
  simp only [CollatzResearch.WordTrace]
  refine ⟨137823538669122030601397003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91882359112748020400931335 137823538669122030601397003)
  ·
    refine ⟨206735308003683045902095505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137823538669122030601397003 206735308003683045902095505)
    ·
      refine ⟨155051481002762284426571629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206735308003683045902095505 155051481002762284426571629)
      ·
        refine ⟨58144305376035856659964361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155051481002762284426571629 58144305376035856659964361)
        ·
          refine ⟨43608229032026892494973271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58144305376035856659964361 43608229032026892494973271)
          ·
            refine ⟨65412343548040338742459907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43608229032026892494973271 65412343548040338742459907)
            ·
              refine ⟨98118515322060508113689861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65412343548040338742459907 98118515322060508113689861)
              ·
                refine ⟨18397221622886345271316849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98118515322060508113689861 18397221622886345271316849)
                ·
                  refine ⟨13797916217164758953487637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18397221622886345271316849 13797916217164758953487637)
                  ·
                    refine ⟨646777322679598075944733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13797916217164758953487637 646777322679598075944733)
                    ·
                      rfl

theorem cell23_3778783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 6].length) (baseStart_3778783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3778783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3778783 prefixEnd_3778783 := by exact prefixLift 3778783
  have htrace : WordTrace (prefixWord ++ tailWord_3778783) baseStart_3778783 baseEnd_3778783 := by
    simpa [prefixWord, tailWord_3778783, baseEnd_3778783] using wordTrace_append hprefix tailTrace_3778783
  have hstable : (prefixWord ++ tailWord_3778783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778783).length < 2 ^ (prefixWord ++ tailWord_3778783).sum := by decide
  have hdescent : baseEnd_3778783 < baseStart_3778783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778840 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 4, 3, 3]
def baseStart_3778840 : Nat := 118140960795 + 3778840 * 2 ^ 59
def prefixEnd_3778840 : Nat := 4983230072969 + 3 ^ 40 * 3778840 * 2
def baseEnd_3778840 : Nat := 1940361236436100504821437

theorem tailTrace_3778840 : CollatzResearch.WordTrace tailWord_3778840 prefixEnd_3778840 1940361236436100504821437 := by
  unfold tailWord_3778840
  simp only [CollatzResearch.WordTrace]
  refine ⟨68912808814957764668110987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91883745086610352890814649 68912808814957764668110987)
  ·
    refine ⟨103369213222436647002166481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68912808814957764668110987 103369213222436647002166481)
    ·
      refine ⟨77526909916827485251624861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103369213222436647002166481 77526909916827485251624861)
      ·
        refine ⟨29072591218810306969359323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77526909916827485251624861 29072591218810306969359323)
        ·
          refine ⟨43608886828215460454038985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29072591218810306969359323 43608886828215460454038985)
          ·
            refine ⟨32706665121161595340529239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43608886828215460454038985 32706665121161595340529239)
            ·
              refine ⟨49059997681742393010793859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32706665121161595340529239 49059997681742393010793859)
              ·
                refine ⟨73589996522613589516190789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49059997681742393010793859 73589996522613589516190789)
                ·
                  refine ⟨13798124347990048034285773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73589996522613589516190789 13798124347990048034285773)
                  ·
                    refine ⟨5174296630496268012857165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13798124347990048034285773 5174296630496268012857165)
                    ·
                      refine ⟨1940361236436100504821437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5174296630496268012857165 1940361236436100504821437)
                      ·
                        rfl

theorem cell23_3778840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_3778840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3778840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3778840 prefixEnd_3778840 := by exact prefixLift 3778840
  have htrace : WordTrace (prefixWord ++ tailWord_3778840) baseStart_3778840 baseEnd_3778840 := by
    simpa [prefixWord, tailWord_3778840, baseEnd_3778840] using wordTrace_append hprefix tailTrace_3778840
  have hstable : (prefixWord ++ tailWord_3778840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778840).length < 2 ^ (prefixWord ++ tailWord_3778840).sum := by decide
  have hdescent : baseEnd_3778840 < baseStart_3778840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778847 : List Nat := [1, 1, 2, 4, 3, 1, 2, 4, 5]
def baseStart_3778847 : Nat := 118140960795 + 3778847 * 2 ^ 59
def prefixEnd_3778847 : Nat := 4983230072969 + 3 ^ 40 * 3778847 * 2
def baseEnd_3778847 : Nat := 215596092311186886381545

theorem tailTrace_3778847 : CollatzResearch.WordTrace tailWord_3778847 prefixEnd_3778847 215596092311186886381545 := by
  unfold tailWord_3778847
  simp only [CollatzResearch.WordTrace]
  refine ⟨137825872940890169531726795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91883915293926779687817863 137825872940890169531726795)
  ·
    refine ⟨206738809411335254297590193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137825872940890169531726795 206738809411335254297590193)
    ·
      refine ⟨155054107058501440723192645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206738809411335254297590193 155054107058501440723192645)
      ·
        refine ⟨29072645073469020135598621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155054107058501440723192645 29072645073469020135598621)
        ·
          refine ⟨10902241902550882550849483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29072645073469020135598621 10902241902550882550849483)
          ·
            refine ⟨16353362853826323826274225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10902241902550882550849483 16353362853826323826274225)
            ·
              refine ⟨12265022140369742869705669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16353362853826323826274225 12265022140369742869705669)
              ·
                refine ⟨2299691651319326788069813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12265022140369742869705669 2299691651319326788069813)
                ·
                  refine ⟨215596092311186886381545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2299691651319326788069813 215596092311186886381545)
                  ·
                    rfl

theorem cell23_3778847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 4, 5].length) (baseStart_3778847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3778847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3778847 prefixEnd_3778847 := by exact prefixLift 3778847
  have htrace : WordTrace (prefixWord ++ tailWord_3778847) baseStart_3778847 baseEnd_3778847 := by
    simpa [prefixWord, tailWord_3778847, baseEnd_3778847] using wordTrace_append hprefix tailTrace_3778847
  have hstable : (prefixWord ++ tailWord_3778847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778847).length < 2 ^ (prefixWord ++ tailWord_3778847).sum := by decide
  have hdescent : baseEnd_3778847 < baseStart_3778847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778858 : List Nat := [3, 1, 4, 2, 3, 1, 1, 1, 1, 4, 2]
def baseStart_3778858 : Nat := 118140960795 + 3778858 * 2 ^ 59
def prefixEnd_3778858 : Nat := 4983230072969 + 3 ^ 40 * 3778858 * 2
def baseEnd_3778858 : Nat := 1940370479087881434396355

theorem tailTrace_3778858 : CollatzResearch.WordTrace tailWord_3778858 prefixEnd_3778858 1940370479087881434396355 := by
  unfold tailWord_3778858
  simp only [CollatzResearch.WordTrace]
  refine ⟨34456568535962579602594307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91884182762566878940251485 34456568535962579602594307)
  ·
    refine ⟨51684852803943869403891461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34456568535962579602594307 51684852803943869403891461)
    ·
      refine ⟨9690909900739475513229649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51684852803943869403891461 9690909900739475513229649)
      ·
        refine ⟨7268182425554606634922237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9690909900739475513229649 7268182425554606634922237)
        ·
          refine ⟨2725568409582977488095839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7268182425554606634922237 2725568409582977488095839)
          ·
            refine ⟨4088352614374466232143759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2725568409582977488095839 4088352614374466232143759)
            ·
              refine ⟨6132528921561699348215639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4088352614374466232143759 6132528921561699348215639)
              ·
                refine ⟨9198793382342549022323459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6132528921561699348215639 9198793382342549022323459)
                ·
                  refine ⟨13798190073513823533485189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9198793382342549022323459 13798190073513823533485189)
                  ·
                    refine ⟨2587160638783841912528473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13798190073513823533485189 2587160638783841912528473)
                    ·
                      refine ⟨1940370479087881434396355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2587160638783841912528473 1940370479087881434396355)
                      ·
                        rfl

theorem cell23_3778858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_3778858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3778858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3778858 prefixEnd_3778858 := by exact prefixLift 3778858
  have htrace : WordTrace (prefixWord ++ tailWord_3778858) baseStart_3778858 baseEnd_3778858 := by
    simpa [prefixWord, tailWord_3778858, baseEnd_3778858] using wordTrace_append hprefix tailTrace_3778858
  have hstable : (prefixWord ++ tailWord_3778858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778858).length < 2 ^ (prefixWord ++ tailWord_3778858).sum := by decide
  have hdescent : baseEnd_3778858 < baseStart_3778858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778881 : List Nat := [1, 2, 5, 2, 2, 2, 1, 3, 5]
def baseStart_3778881 : Nat := 118140960795 + 3778881 * 2 ^ 59
def prefixEnd_3778881 : Nat := 4983230072969 + 3 ^ 40 * 3778881 * 2
def baseEnd_3778881 : Nat := 215598032126992760489861

theorem tailTrace_3778881 : CollatzResearch.WordTrace tailWord_3778881 prefixEnd_3778881 215598032126992760489861 := by
  unfold tailWord_3778881
  simp only [CollatzResearch.WordTrace]
  refine ⟨137827113022766993338464497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91884742015177995558976331 137827113022766993338464497)
  ·
    refine ⟨103370334767075245003848373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137827113022766993338464497 103370334767075245003848373)
    ·
      refine ⟨9690968884413304219110785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103370334767075245003848373 9690968884413304219110785)
      ·
        refine ⟨7268226663309978164333089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9690968884413304219110785 7268226663309978164333089)
        ·
          refine ⟨5451169997482483623249817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7268226663309978164333089 5451169997482483623249817)
          ·
            refine ⟨4088377498111862717437363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5451169997482483623249817 4088377498111862717437363)
            ·
              refine ⟨6132566247167794076156045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4088377498111862717437363 6132566247167794076156045)
              ·
                refine ⟨2299712342687922778558517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6132566247167794076156045 2299712342687922778558517)
                ·
                  refine ⟨215598032126992760489861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2299712342687922778558517 215598032126992760489861)
                  ·
                    rfl

theorem cell23_3778881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 3, 5].length) (baseStart_3778881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3778881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3778881 prefixEnd_3778881 := by exact prefixLift 3778881
  have htrace : WordTrace (prefixWord ++ tailWord_3778881) baseStart_3778881 baseEnd_3778881 := by
    simpa [prefixWord, tailWord_3778881, baseEnd_3778881] using wordTrace_append hprefix tailTrace_3778881
  have hstable : (prefixWord ++ tailWord_3778881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778881).length < 2 ^ (prefixWord ++ tailWord_3778881).sum := by decide
  have hdescent : baseEnd_3778881 < baseStart_3778881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778897 : List Nat := [1, 2, 2, 1, 4, 3, 1, 2, 2, 1, 4]
def baseStart_3778897 : Nat := 118140960795 + 3778897 * 2 ^ 59
def prefixEnd_3778897 : Nat := 4983230072969 + 3 ^ 40 * 3778897 * 2
def baseEnd_3778897 : Nat := 1940390504833406781808675

theorem tailTrace_3778897 : CollatzResearch.WordTrace tailWord_3778897 prefixEnd_3778897 1940390504833406781808675 := by
  unfold tailWord_3778897
  simp only [CollatzResearch.WordTrace]
  refine ⟨137827696590709028071046945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91885131060472685380697963 137827696590709028071046945)
  ·
    refine ⟨103370772443031771053285209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137827696590709028071046945 103370772443031771053285209)
    ·
      refine ⟨77528079332273828289963907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103370772443031771053285209 77528079332273828289963907)
      ·
        refine ⟨116292118998410742434945861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77528079332273828289963907 116292118998410742434945861)
        ·
          refine ⟨21804772312202014206552349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116292118998410742434945861 21804772312202014206552349)
          ·
            refine ⟨8176789617075755327457131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21804772312202014206552349 8176789617075755327457131)
            ·
              refine ⟨12265184425613632991185697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8176789617075755327457131 12265184425613632991185697)
              ·
                refine ⟨9198888319210224743389273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12265184425613632991185697 9198888319210224743389273)
                ·
                  refine ⟨6899166239407668557541955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9198888319210224743389273 6899166239407668557541955)
                  ·
                    refine ⟨10348749359111502836312933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6899166239407668557541955 10348749359111502836312933)
                    ·
                      refine ⟨1940390504833406781808675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10348749359111502836312933 1940390504833406781808675)
                      ·
                        rfl

theorem cell23_3778897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 1, 4].length) (baseStart_3778897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3778897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3778897 prefixEnd_3778897 := by exact prefixLift 3778897
  have htrace : WordTrace (prefixWord ++ tailWord_3778897) baseStart_3778897 baseEnd_3778897 := by
    simpa [prefixWord, tailWord_3778897, baseEnd_3778897] using wordTrace_append hprefix tailTrace_3778897
  have hstable : (prefixWord ++ tailWord_3778897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778897).length < 2 ^ (prefixWord ++ tailWord_3778897).sum := by decide
  have hdescent : baseEnd_3778897 < baseStart_3778897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778958 : List Nat := [4, 1, 1, 4, 1, 1, 4, 2, 1, 4]
def baseStart_3778958 : Nat := 118140960795 + 3778958 * 2 ^ 59
def prefixEnd_3778958 : Nat := 4983230072969 + 3 ^ 40 * 3778958 * 2
def baseEnd_3778958 : Nat := 646807275717777014381965

theorem tailTrace_3778958 : CollatzResearch.WordTrace tailWord_3778958 prefixEnd_3778958 646807275717777014381965 := by
  unfold tailWord_3778958
  simp only [CollatzResearch.WordTrace]
  refine ⟨17228740180436004436127191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91886614295658690326011685 17228740180436004436127191)
  ·
    refine ⟨25843110270654006654190787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17228740180436004436127191 25843110270654006654190787)
    ·
      refine ⟨38764665405981009981286181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25843110270654006654190787 38764665405981009981286181)
      ·
        refine ⟨7268374763621439371491159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38764665405981009981286181 7268374763621439371491159)
        ·
          refine ⟨10902562145432159057236739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7268374763621439371491159 10902562145432159057236739)
          ·
            refine ⟨16353843218148238585855109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10902562145432159057236739 16353843218148238585855109)
            ·
              refine ⟨3066345603402794734847833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16353843218148238585855109 3066345603402794734847833)
              ·
                refine ⟨2299759202552096051135875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3066345603402794734847833 2299759202552096051135875)
                ·
                  refine ⟨3449638803828144076703813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2299759202552096051135875 3449638803828144076703813)
                  ·
                    refine ⟨646807275717777014381965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3449638803828144076703813 646807275717777014381965)
                    ·
                      rfl

theorem cell23_3778958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 2, 1, 4].length) (baseStart_3778958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3778958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3778958 prefixEnd_3778958 := by exact prefixLift 3778958
  have htrace : WordTrace (prefixWord ++ tailWord_3778958) baseStart_3778958 baseEnd_3778958 := by
    simpa [prefixWord, tailWord_3778958, baseEnd_3778958] using wordTrace_append hprefix tailTrace_3778958
  have hstable : (prefixWord ++ tailWord_3778958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778958).length < 2 ^ (prefixWord ++ tailWord_3778958).sum := by decide
  have hdescent : baseEnd_3778958 < baseStart_3778958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3778984 : List Nat := [2, 1, 6, 1, 1, 1, 2, 1, 3, 5]
def baseStart_3778984 : Nat := 118140960795 + 3778984 * 2 ^ 59
def prefixEnd_3778984 : Nat := 4983230072969 + 3 ^ 40 * 3778984 * 2
def baseEnd_3778984 : Nat := 646811725883449313806925

theorem tailTrace_3778984 : CollatzResearch.WordTrace tailWord_3778984 prefixEnd_3778984 646811725883449313806925 := by
  unfold tailWord_3778984
  simp only [CollatzResearch.WordTrace]
  refine ⟨68915434870696920964732003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91887246494262561286309337 68915434870696920964732003)
  ·
    refine ⟨103373152306045381447098005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68915434870696920964732003 103373152306045381447098005)
    ·
      refine ⟨4845616514345877255332719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 103373152306045381447098005 4845616514345877255332719)
      ·
        refine ⟨7268424771518815882999079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4845616514345877255332719 7268424771518815882999079)
        ·
          refine ⟨10902637157278223824498619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7268424771518815882999079 10902637157278223824498619)
          ·
            refine ⟨16353955735917335736747929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10902637157278223824498619 16353955735917335736747929)
            ·
              refine ⟨12265466801938001802560947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16353955735917335736747929 12265466801938001802560947)
              ·
                refine ⟨18398200202907002703841421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12265466801938001802560947 18398200202907002703841421)
                ·
                  refine ⟨6899325076090126013940533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18398200202907002703841421 6899325076090126013940533)
                  ·
                    refine ⟨646811725883449313806925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6899325076090126013940533 646811725883449313806925)
                    ·
                      rfl

theorem cell23_3778984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_3778984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3778984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3778984 prefixEnd_3778984 := by exact prefixLift 3778984
  have htrace : WordTrace (prefixWord ++ tailWord_3778984) baseStart_3778984 baseEnd_3778984 := by
    simpa [prefixWord, tailWord_3778984, baseEnd_3778984] using wordTrace_append hprefix tailTrace_3778984
  have hstable : (prefixWord ++ tailWord_3778984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3778984).length < 2 ^ (prefixWord ++ tailWord_3778984).sum := by decide
  have hdescent : baseEnd_3778984 < baseStart_3778984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3778984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779000 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 3, 1, 6]
def baseStart_3779000 : Nat := 118140960795 + 3779000 * 2 ^ 59
def prefixEnd_3779000 : Nat := 4983230072969 + 3 ^ 40 * 3779000 * 2
def baseEnd_3779000 : Nat := 1940443393340819878820701

theorem tailTrace_3779000 : CollatzResearch.WordTrace tailWord_3779000 prefixEnd_3779000 1940443393340819878820701 := by
  unfold tailWord_3779000
  simp only [CollatzResearch.WordTrace]
  refine ⟨68915726654667938331023227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91887635539557251108030969 68915726654667938331023227)
  ·
    refine ⟨103373589982001907496534841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68915726654667938331023227 103373589982001907496534841)
    ·
      refine ⟨77530192486501430622401131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103373589982001907496534841 77530192486501430622401131)
      ·
        refine ⟨116295288729752145933601697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77530192486501430622401131 116295288729752145933601697)
        ·
          refine ⟨87221466547314109450201273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116295288729752145933601697 87221466547314109450201273)
          ·
            refine ⟨65416099910485582087650955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87221466547314109450201273 65416099910485582087650955)
            ·
              refine ⟨98124149865728373131476433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65416099910485582087650955 98124149865728373131476433)
              ·
                refine ⟨73593112399296279848607325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98124149865728373131476433 73593112399296279848607325)
                ·
                  refine ⟨27597417149736104943227747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73593112399296279848607325 27597417149736104943227747)
                  ·
                    refine ⟨41396125724604157414841621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27597417149736104943227747 41396125724604157414841621)
                    ·
                      refine ⟨1940443393340819878820701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41396125724604157414841621 1940443393340819878820701)
                      ·
                        rfl

theorem cell23_3779000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_3779000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779000 prefixEnd_3779000 := by exact prefixLift 3779000
  have htrace : WordTrace (prefixWord ++ tailWord_3779000) baseStart_3779000 baseEnd_3779000 := by
    simpa [prefixWord, tailWord_3779000, baseEnd_3779000] using wordTrace_append hprefix tailTrace_3779000
  have hstable : (prefixWord ++ tailWord_3779000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779000).length < 2 ^ (prefixWord ++ tailWord_3779000).sum := by decide
  have hdescent : baseEnd_3779000 < baseStart_3779000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779001 : List Nat := [1, 2, 1, 4, 3, 3, 2, 1, 1, 5]
def baseStart_3779001 : Nat := 118140960795 + 3779001 * 2 ^ 59
def prefixEnd_3779001 : Nat := 4983230072969 + 3 ^ 40 * 3779001 * 2
def baseEnd_3779001 : Nat := 646814635607158124969399

theorem tailTrace_3779001 : CollatzResearch.WordTrace tailWord_3779001 prefixEnd_3779001 646814635607158124969399 := by
  unfold tailWord_3779001
  simp only [CollatzResearch.WordTrace]
  refine ⟨137831489782332253832832857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91887659854888169221888571 137831489782332253832832857)
  ·
    refine ⟨103373617336749190374624643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137831489782332253832832857 103373617336749190374624643)
    ·
      refine ⟨155060426005123785561936965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103373617336749190374624643 155060426005123785561936965)
      ·
        refine ⟨29073829875960709792863181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155060426005123785561936965 29073829875960709792863181)
        ·
          refine ⟨10902686203485266172323693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29073829875960709792863181 10902686203485266172323693)
          ·
            refine ⟨4088507326306974814621385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10902686203485266172323693 4088507326306974814621385)
            ·
              refine ⟨3066380494730231110966039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4088507326306974814621385 3066380494730231110966039)
              ·
                refine ⟨4599570742095346666449059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3066380494730231110966039 4599570742095346666449059)
                ·
                  refine ⟨6899356113143019999673589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4599570742095346666449059 6899356113143019999673589)
                  ·
                    refine ⟨646814635607158124969399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6899356113143019999673589 646814635607158124969399)
                    ·
                      rfl

theorem cell23_3779001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 1, 5].length) (baseStart_3779001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779001 prefixEnd_3779001 := by exact prefixLift 3779001
  have htrace : WordTrace (prefixWord ++ tailWord_3779001) baseStart_3779001 baseEnd_3779001 := by
    simpa [prefixWord, tailWord_3779001, baseEnd_3779001] using wordTrace_append hprefix tailTrace_3779001
  have hstable : (prefixWord ++ tailWord_3779001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779001).length < 2 ^ (prefixWord ++ tailWord_3779001).sum := by decide
  have hdescent : baseEnd_3779001 < baseStart_3779001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779061 : List Nat := [1, 3, 5, 1, 3, 1, 9]
def baseStart_3779061 : Nat := 118140960795 + 3779061 * 2 ^ 59
def prefixEnd_3779061 : Nat := 4983230072969 + 3 ^ 40 * 3779061 * 2
def baseEnd_3779061 : Nat := 23956477971120298026641

theorem tailTrace_3779061 : CollatzResearch.WordTrace tailWord_3779061 prefixEnd_3779061 23956477971120298026641 := by
  unfold tailWord_3779061
  simp only [CollatzResearch.WordTrace]
  refine ⟨137833678162114884080017037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91889118774743256053344691 137833678162114884080017037)
  ·
    refine ⟨51687629310793081530006389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137833678162114884080017037 51687629310793081530006389)
    ·
      refine ⟨4845715247886851393438099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51687629310793081530006389 4845715247886851393438099)
      ·
        refine ⟨7268572871830277090157149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4845715247886851393438099 7268572871830277090157149)
        ·
          refine ⟨2725714826936353908808931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7268572871830277090157149 2725714826936353908808931)
          ·
            refine ⟨4088572240404530863213397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2725714826936353908808931 4088572240404530863213397)
            ·
              refine ⟨23956477971120298026641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4088572240404530863213397 23956477971120298026641)
              ·
                rfl

theorem cell23_3779061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 9].length) (baseStart_3779061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779061 prefixEnd_3779061 := by exact prefixLift 3779061
  have htrace : WordTrace (prefixWord ++ tailWord_3779061) baseStart_3779061 baseEnd_3779061 := by
    simpa [prefixWord, tailWord_3779061, baseEnd_3779061] using wordTrace_append hprefix tailTrace_3779061
  have hstable : (prefixWord ++ tailWord_3779061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779061).length < 2 ^ (prefixWord ++ tailWord_3779061).sum := by decide
  have hdescent : baseEnd_3779061 < baseStart_3779061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779078 : List Nat := [6, 2, 1, 1, 1, 2, 2, 8]
def baseStart_3779078 : Nat := 118140960795 + 3779078 * 2 ^ 59
def prefixEnd_3779078 : Nat := 4983230072969 + 3 ^ 40 * 3779078 * 2
def baseEnd_3779078 : Nat := 71869757215995206431309

theorem tailTrace_3779078 : CollatzResearch.WordTrace tailWord_3779078 prefixEnd_3779078 71869757215995206431309 := by
  unfold tailWord_3779078
  simp only [CollatzResearch.WordTrace]
  refine ⟨4307321818845415499480809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 91889532135368863988923925 4307321818845415499480809)
  ·
    refine ⟨3230491364134061624610607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4307321818845415499480809 3230491364134061624610607)
    ·
      refine ⟨4845737046201092436915911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3230491364134061624610607 4845737046201092436915911)
      ·
        refine ⟨7268605569301638655373867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4845737046201092436915911 7268605569301638655373867)
        ·
          refine ⟨10902908353952457983060801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7268605569301638655373867 10902908353952457983060801)
          ·
            refine ⟨8177181265464343487295601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10902908353952457983060801 8177181265464343487295601)
            ·
              refine ⟨6132885949098257615471701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8177181265464343487295601 6132885949098257615471701)
              ·
                refine ⟨71869757215995206431309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6132885949098257615471701 71869757215995206431309)
                ·
                  rfl

theorem cell23_3779078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_3779078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779078 prefixEnd_3779078 := by exact prefixLift 3779078
  have htrace : WordTrace (prefixWord ++ tailWord_3779078) baseStart_3779078 baseEnd_3779078 := by
    simpa [prefixWord, tailWord_3779078, baseEnd_3779078] using wordTrace_append hprefix tailTrace_3779078
  have hstable : (prefixWord ++ tailWord_3779078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779078).length < 2 ^ (prefixWord ++ tailWord_3779078).sum := by decide
  have hdescent : baseEnd_3779078 < baseStart_3779078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779097 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 2, 4, 3]
def baseStart_3779097 : Nat := 118140960795 + 3779097 * 2 ^ 59
def prefixEnd_3779097 : Nat := 4983230072969 + 3 ^ 40 * 3779097 * 2
def baseEnd_3779097 : Nat := 1940493200964305999307755

theorem tailTrace_3779097 : CollatzResearch.WordTrace tailWord_3779097 prefixEnd_3779097 1940493200964305999307755 := by
  unfold tailWord_3779097
  simp only [CollatzResearch.WordTrace]
  refine ⟨137834991189984462228327545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91889994126656308152218363 137834991189984462228327545)
  ·
    refine ⟨103376243392488346671245659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137834991189984462228327545 103376243392488346671245659)
    ·
      refine ⟨155064365088732520006868489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103376243392488346671245659 155064365088732520006868489)
      ·
        refine ⟨116298273816549390005151367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155064365088732520006868489 116298273816549390005151367)
        ·
          refine ⟨174447410724824085007727051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116298273816549390005151367 174447410724824085007727051)
          ·
            refine ⟨261671116087236127511590577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174447410724824085007727051 261671116087236127511590577)
            ·
              refine ⟨196253337065427095633692933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261671116087236127511590577 196253337065427095633692933)
              ·
                refine ⟨36797500699767580431317425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 196253337065427095633692933 36797500699767580431317425)
                ·
                  refine ⟨27598125524825685323488069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36797500699767580431317425 27598125524825685323488069)
                  ·
                    refine ⟨5174648535904815998154013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27598125524825685323488069 5174648535904815998154013)
                    ·
                      refine ⟨1940493200964305999307755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5174648535904815998154013 1940493200964305999307755)
                      ·
                        rfl

theorem cell23_3779097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 4, 3].length) (baseStart_3779097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779097 prefixEnd_3779097 := by exact prefixLift 3779097
  have htrace : WordTrace (prefixWord ++ tailWord_3779097) baseStart_3779097 baseEnd_3779097 := by
    simpa [prefixWord, tailWord_3779097, baseEnd_3779097] using wordTrace_append hprefix tailTrace_3779097
  have hstable : (prefixWord ++ tailWord_3779097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779097).length < 2 ^ (prefixWord ++ tailWord_3779097).sum := by decide
  have hdescent : baseEnd_3779097 < baseStart_3779097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779114 : List Nat := [3, 1, 4, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_3779114 : Nat := 118140960795 + 3779114 * 2 ^ 59
def prefixEnd_3779114 : Nat := 4983230072969 + 3 ^ 40 * 3779114 * 2
def baseEnd_3779114 : Nat := 1940501930135432432795177

theorem tailTrace_3779114 : CollatzResearch.WordTrace tailWord_3779114 prefixEnd_3779114 1940501930135432432795177 := by
  unfold tailWord_3779114
  simp only [CollatzResearch.WordTrace]
  refine ⟨34458902807730718532924099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91890407487281916087797597 34458902807730718532924099)
  ·
    refine ⟨51688354211596077799386149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34458902807730718532924099 51688354211596077799386149)
    ·
      refine ⟨9691566414674264587384903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51688354211596077799386149 9691566414674264587384903)
      ·
        refine ⟨14537349622011396881077355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9691566414674264587384903 14537349622011396881077355)
        ·
          refine ⟨21806024433017095321616033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14537349622011396881077355 21806024433017095321616033)
          ·
            refine ⟨16354518324762821491212025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21806024433017095321616033 16354518324762821491212025)
            ·
              refine ⟨12265888743572116118409019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16354518324762821491212025 12265888743572116118409019)
              ·
                refine ⟨18398833115358174177613529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12265888743572116118409019 18398833115358174177613529)
                ·
                  refine ⟨13799124836518630633210147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18398833115358174177613529 13799124836518630633210147)
                  ·
                    refine ⟨20698687254777945949815221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13799124836518630633210147 20698687254777945949815221)
                    ·
                      refine ⟨1940501930135432432795177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20698687254777945949815221 1940501930135432432795177)
                      ·
                        rfl

theorem cell23_3779114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_3779114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779114 prefixEnd_3779114 := by exact prefixLift 3779114
  have htrace : WordTrace (prefixWord ++ tailWord_3779114) baseStart_3779114 baseEnd_3779114 := by
    simpa [prefixWord, tailWord_3779114, baseEnd_3779114] using wordTrace_append hprefix tailTrace_3779114
  have hstable : (prefixWord ++ tailWord_3779114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779114).length < 2 ^ (prefixWord ++ tailWord_3779114).sum := by decide
  have hdescent : baseEnd_3779114 < baseStart_3779114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779128 : List Nat := [2, 1, 2, 1, 4, 1, 4, 2, 2, 2, 2]
def baseStart_3779128 : Nat := 118140960795 + 3779128 * 2 ^ 59
def prefixEnd_3779128 : Nat := 4983230072969 + 3 ^ 40 * 3779128 * 2
def baseEnd_3779128 : Nat := 1940509118864595378020113

theorem tailTrace_3779128 : CollatzResearch.WordTrace tailWord_3779128 prefixEnd_3779128 1940509118864595378020113 := by
  unfold tailWord_3779128
  simp only [CollatzResearch.WordTrace]
  refine ⟨68918060926436077261353019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91890747901914769681804025 68918060926436077261353019)
  ·
    refine ⟨103377091389654115892029529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68918060926436077261353019 103377091389654115892029529)
    ·
      refine ⟨77532818542240586919022147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103377091389654115892029529 77532818542240586919022147)
      ·
        refine ⟨116299227813360880378533221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77532818542240586919022147 116299227813360880378533221)
        ·
          refine ⟨21806105215005165070974979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116299227813360880378533221 21806105215005165070974979)
          ·
            refine ⟨32709157822507747606462469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21806105215005165070974979 32709157822507747606462469)
            ·
              refine ⟨6132967091720202676211713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32709157822507747606462469 6132967091720202676211713)
              ·
                refine ⟨4599725318790152007158785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6132967091720202676211713 4599725318790152007158785)
                ·
                  refine ⟨3449793989092614005369089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4599725318790152007158785 3449793989092614005369089)
                  ·
                    refine ⟨2587345491819460504026817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3449793989092614005369089 2587345491819460504026817)
                    ·
                      refine ⟨1940509118864595378020113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2587345491819460504026817 1940509118864595378020113)
                      ·
                        rfl

theorem cell23_3779128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 2, 2, 2].length) (baseStart_3779128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779128 prefixEnd_3779128 := by exact prefixLift 3779128
  have htrace : WordTrace (prefixWord ++ tailWord_3779128) baseStart_3779128 baseEnd_3779128 := by
    simpa [prefixWord, tailWord_3779128, baseEnd_3779128] using wordTrace_append hprefix tailTrace_3779128
  have hstable : (prefixWord ++ tailWord_3779128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779128).length < 2 ^ (prefixWord ++ tailWord_3779128).sum := by decide
  have hdescent : baseEnd_3779128 < baseStart_3779128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779147 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 4, 5]
def baseStart_3779147 : Nat := 118140960795 + 3779147 * 2 ^ 59
def prefixEnd_3779147 : Nat := 4983230072969 + 3 ^ 40 * 3779147 * 2
def baseEnd_3779147 : Nat := 646839624999010267894175

theorem tailTrace_3779147 : CollatzResearch.WordTrace tailWord_3779147 prefixEnd_3779147 646839624999010267894175 := by
  unfold tailWord_3779147
  simp only [CollatzResearch.WordTrace]
  refine ⟨137836814839803320767647695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91891209893202213845098463 137836814839803320767647695)
  ·
    refine ⟨206755222259704981151471543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137836814839803320767647695 206755222259704981151471543)
    ·
      refine ⟨310132833389557471727207315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206755222259704981151471543 310132833389557471727207315)
      ·
        refine ⟨465199250084336207590810973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310132833389557471727207315 465199250084336207590810973)
        ·
          refine ⟨174449718781626077846554115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 465199250084336207590810973 174449718781626077846554115)
          ·
            refine ⟨261674578172439116769831173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174449718781626077846554115 261674578172439116769831173)
            ·
              refine ⟨49063983407332334394343345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 261674578172439116769831173 49063983407332334394343345)
              ·
                refine ⟨36797987555499250795757509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49063983407332334394343345 36797987555499250795757509)
                ·
                  refine ⟨6899622666656109524204533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36797987555499250795757509 6899622666656109524204533)
                  ·
                    refine ⟨646839624999010267894175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6899622666656109524204533 646839624999010267894175)
                    ·
                      rfl

theorem cell23_3779147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 5].length) (baseStart_3779147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779147 prefixEnd_3779147 := by exact prefixLift 3779147
  have htrace : WordTrace (prefixWord ++ tailWord_3779147) baseStart_3779147 baseEnd_3779147 := by
    simpa [prefixWord, tailWord_3779147, baseEnd_3779147] using wordTrace_append hprefix tailTrace_3779147
  have hstable : (prefixWord ++ tailWord_3779147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779147).length < 2 ^ (prefixWord ++ tailWord_3779147).sum := by decide
  have hdescent : baseEnd_3779147 < baseStart_3779147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779157 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 1, 1, 7]
def baseStart_3779157 : Nat := 118140960795 + 3779157 * 2 ^ 59
def prefixEnd_3779157 : Nat := 4983230072969 + 3 ^ 40 * 3779157 * 2
def baseEnd_3779157 : Nat := 1940524009803575764557479

theorem tailTrace_3779157 : CollatzResearch.WordTrace tailWord_3779157 prefixEnd_3779157 1940524009803575764557479 := by
  unfold tailWord_3779157
  simp only [CollatzResearch.WordTrace]
  refine ⟨137837179569767092475511725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91891453046511394983674483 137837179569767092475511725)
  ·
    refine ⟨51688942338662659678316897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137837179569767092475511725 51688942338662659678316897)
    ·
      refine ⟨38766706753996994758737673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51688942338662659678316897 38766706753996994758737673)
      ·
        refine ⟨29075030065497746069053255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38766706753996994758737673 29075030065497746069053255)
        ·
          refine ⟨43612545098246619103579883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29075030065497746069053255 43612545098246619103579883)
          ·
            refine ⟨65418817647369928655369825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43612545098246619103579883 65418817647369928655369825)
            ·
              refine ⟨49064113235527446491527369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65418817647369928655369825 49064113235527446491527369)
              ·
                refine ⟨36798084926645584868645527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49064113235527446491527369 36798084926645584868645527)
                ·
                  refine ⟨55197127389968377302968291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36798084926645584868645527 55197127389968377302968291)
                  ·
                    refine ⟨82795691084952565954452437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55197127389968377302968291 82795691084952565954452437)
                    ·
                      refine ⟨1940524009803575764557479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 82795691084952565954452437 1940524009803575764557479)
                      ·
                        rfl

theorem cell23_3779157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_3779157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779157 prefixEnd_3779157 := by exact prefixLift 3779157
  have htrace : WordTrace (prefixWord ++ tailWord_3779157) baseStart_3779157 baseEnd_3779157 := by
    simpa [prefixWord, tailWord_3779157, baseEnd_3779157] using wordTrace_append hprefix tailTrace_3779157
  have hstable : (prefixWord ++ tailWord_3779157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779157).length < 2 ^ (prefixWord ++ tailWord_3779157).sum := by decide
  have hdescent : baseEnd_3779157 < baseStart_3779157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3779166 : List Nat := [4, 4, 1, 2, 1, 2, 2, 1, 1, 3, 2]
def baseStart_3779166 : Nat := 118140960795 + 3779166 * 2 ^ 59
def prefixEnd_3779166 : Nat := 4983230072969 + 3 ^ 40 * 3779166 * 2
def baseEnd_3779166 : Nat := 1940528631129466229344939

theorem tailTrace_3779166 : CollatzResearch.WordTrace tailWord_3779166 prefixEnd_3779166 1940528631129466229344939 := by
  unfold tailWord_3779166
  simp only [CollatzResearch.WordTrace]
  refine ⟨17229688478341810876573669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91891671884489658008392901 17229688478341810876573669)
  ·
    refine ⟨3230566589689089539357563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17229688478341810876573669 3230566589689089539357563)
    ·
      refine ⟨4845849884533634309036345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3230566589689089539357563 4845849884533634309036345)
      ·
        refine ⟨3634387413400225731777259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4845849884533634309036345 3634387413400225731777259)
        ·
          refine ⟨5451581120100338597665889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3634387413400225731777259 5451581120100338597665889)
          ·
            refine ⟨4088685840075253948249417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5451581120100338597665889 4088685840075253948249417)
            ·
              refine ⟨3066514380056440461187063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4088685840075253948249417 3066514380056440461187063)
              ·
                refine ⟨4599771570084660691780595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3066514380056440461187063 4599771570084660691780595)
                ·
                  refine ⟨6899657355126991037670893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4599771570084660691780595 6899657355126991037670893)
                  ·
                    refine ⟨2587371508172621639126585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6899657355126991037670893 2587371508172621639126585)
                    ·
                      refine ⟨1940528631129466229344939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2587371508172621639126585 1940528631129466229344939)
                      ·
                        rfl

theorem cell23_3779166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_3779166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3779166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3779166 prefixEnd_3779166 := by exact prefixLift 3779166
  have htrace : WordTrace (prefixWord ++ tailWord_3779166) baseStart_3779166 baseEnd_3779166 := by
    simpa [prefixWord, tailWord_3779166, baseEnd_3779166] using wordTrace_append hprefix tailTrace_3779166
  have hstable : (prefixWord ++ tailWord_3779166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3779166).length < 2 ^ (prefixWord ++ tailWord_3779166).sum := by decide
  have hdescent : baseEnd_3779166 < baseStart_3779166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3779166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
