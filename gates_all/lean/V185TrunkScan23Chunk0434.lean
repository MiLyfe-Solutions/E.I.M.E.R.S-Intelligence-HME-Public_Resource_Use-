import V185TrunkScan23Chunk0433

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2566343 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 7]
def baseStart_2566343 : Nat := 118140960795 + 2566343 * 2 ^ 59
def prefixEnd_2566343 : Nat := 4983230072969 + 3 ^ 40 * 2566343 * 2
def baseEnd_2566343 : Nat := 1317767483301557904910109

theorem tailTrace_2566343 : CollatzResearch.WordTrace tailWord_2566343 prefixEnd_2566343 1317767483301557904910109 := by
  unfold tailWord_2566343
  simp only [CollatzResearch.WordTrace]
  refine ⟨93602218941585082334943683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62401479294390054889962455 93602218941585082334943683)
  ·
    refine ⟨140403328412377623502415525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93602218941585082334943683 140403328412377623502415525)
    ·
      refine ⟨26325624077320804406702911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140403328412377623502415525 26325624077320804406702911)
      ·
        refine ⟨39488436115981206610054367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26325624077320804406702911 39488436115981206610054367)
        ·
          refine ⟨59232654173971809915081551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39488436115981206610054367 59232654173971809915081551)
          ·
            refine ⟨88848981260957714872622327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59232654173971809915081551 88848981260957714872622327)
            ·
              refine ⟨133273471891436572308933491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88848981260957714872622327 133273471891436572308933491)
              ·
                refine ⟨199910207837154858463400237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133273471891436572308933491 199910207837154858463400237)
                ·
                  refine ⟨74966327938933071923775089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 199910207837154858463400237 74966327938933071923775089)
                  ·
                    refine ⟨56224745954199803942831317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74966327938933071923775089 56224745954199803942831317)
                    ·
                      refine ⟨1317767483301557904910109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 56224745954199803942831317 1317767483301557904910109)
                      ·
                        rfl

theorem cell23_2566343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_2566343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566343 prefixEnd_2566343 := by exact prefixLift 2566343
  have htrace : WordTrace (prefixWord ++ tailWord_2566343) baseStart_2566343 baseEnd_2566343 := by
    simpa [prefixWord, tailWord_2566343, baseEnd_2566343] using wordTrace_append hprefix tailTrace_2566343
  have hstable : (prefixWord ++ tailWord_2566343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566343).length < 2 ^ (prefixWord ++ tailWord_2566343).sum := by decide
  have hdescent : baseEnd_2566343 < baseStart_2566343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566363 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 3, 7]
def baseStart_2566363 : Nat := 118140960795 + 2566363 * 2 ^ 59
def prefixEnd_2566363 : Nat := 4983230072969 + 3 ^ 40 * 2566363 * 2
def baseEnd_2566363 : Nat := 439259250971549275553339

theorem tailTrace_2566363 : CollatzResearch.WordTrace tailWord_2566363 prefixEnd_2566363 439259250971549275553339 := by
  unfold tailWord_2566363
  simp only [CollatzResearch.WordTrace]
  refine ⟨93602948401512625750671743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62401965601008417167114495 93602948401512625750671743)
  ·
    refine ⟨140404422602268938626007615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93602948401512625750671743 140404422602268938626007615)
    ·
      refine ⟨210606633903403407939011423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140404422602268938626007615 210606633903403407939011423)
      ·
        refine ⟨315909950855105111908517135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210606633903403407939011423 315909950855105111908517135)
        ·
          refine ⟨473864926282657667862775703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315909950855105111908517135 473864926282657667862775703)
          ·
            refine ⟨710797389423986501794163555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473864926282657667862775703 710797389423986501794163555)
            ·
              refine ⟨1066196084135979752691245333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 710797389423986501794163555 1066196084135979752691245333)
              ·
                refine ⟨49977941443874050907402125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1066196084135979752691245333 49977941443874050907402125)
                ·
                  refine ⟨18741728041452769090275797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49977941443874050907402125 18741728041452769090275797)
                  ·
                    refine ⟨439259250971549275553339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18741728041452769090275797 439259250971549275553339)
                    ·
                      rfl

theorem cell23_2566363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 7].length) (baseStart_2566363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566363 prefixEnd_2566363 := by exact prefixLift 2566363
  have htrace : WordTrace (prefixWord ++ tailWord_2566363) baseStart_2566363 baseEnd_2566363 := by
    simpa [prefixWord, tailWord_2566363, baseEnd_2566363] using wordTrace_append hprefix tailTrace_2566363
  have hstable : (prefixWord ++ tailWord_2566363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566363).length < 2 ^ (prefixWord ++ tailWord_2566363).sum := by decide
  have hdescent : baseEnd_2566363 < baseStart_2566363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566400 : List Nat := [2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 4]
def baseStart_2566400 : Nat := 118140960795 + 2566400 * 2 ^ 59
def prefixEnd_2566400 : Nat := 4983230072969 + 3 ^ 40 * 2566400 * 2
def baseEnd_2566400 : Nat := 1317796751698864181897347

theorem tailTrace_2566400 : CollatzResearch.WordTrace tailWord_2566400 prefixEnd_2566400 1317796751698864181897347 := by
  unfold tailWord_2566400
  simp only [CollatzResearch.WordTrace]
  refine ⟨46802148951189290534884327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62402865268252387379845769 46802148951189290534884327)
  ·
    refine ⟨70203223426783935802326491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46802148951189290534884327 70203223426783935802326491)
    ·
      refine ⟨105304835140175903703489737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70203223426783935802326491 105304835140175903703489737)
      ·
        refine ⟨78978626355131927777617303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105304835140175903703489737 78978626355131927777617303)
        ·
          refine ⟨118467939532697891666425955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78978626355131927777617303 118467939532697891666425955)
          ·
            refine ⟨177701909299046837499638933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118467939532697891666425955 177701909299046837499638933)
            ·
              refine ⟨8329776998392820507795575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 177701909299046837499638933 8329776998392820507795575)
              ·
                refine ⟨12494665497589230761693363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8329776998392820507795575 12494665497589230761693363)
                ·
                  refine ⟨18741998246383846142540045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12494665497589230761693363 18741998246383846142540045)
                  ·
                    refine ⟨7028249342393942303452517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18741998246383846142540045 7028249342393942303452517)
                    ·
                      refine ⟨1317796751698864181897347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7028249342393942303452517 1317796751698864181897347)
                      ·
                        rfl

theorem cell23_2566400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_2566400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566400 prefixEnd_2566400 := by exact prefixLift 2566400
  have htrace : WordTrace (prefixWord ++ tailWord_2566400) baseStart_2566400 baseEnd_2566400 := by
    simpa [prefixWord, tailWord_2566400, baseEnd_2566400] using wordTrace_append hprefix tailTrace_2566400
  have hstable : (prefixWord ++ tailWord_2566400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566400).length < 2 ^ (prefixWord ++ tailWord_2566400).sum := by decide
  have hdescent : baseEnd_2566400 < baseStart_2566400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566417 : List Nat := [1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 4]
def baseStart_2566417 : Nat := 118140960795 + 2566417 * 2 ^ 59
def prefixEnd_2566417 : Nat := 4983230072969 + 3 ^ 40 * 2566417 * 2
def baseEnd_2566417 : Nat := 1317805480869990615384769

theorem tailTrace_2566417 : CollatzResearch.WordTrace tailWord_2566417 prefixEnd_2566417 1317805480869990615384769 := by
  unfold tailWord_2566417
  simp only [CollatzResearch.WordTrace]
  refine ⟨93604917943316992973137505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62403278628877995315425003 93604917943316992973137505)
  ·
    refine ⟨70203688457487744729853129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93604917943316992973137505 70203688457487744729853129)
    ·
      refine ⟨52652766343115808547389847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70203688457487744729853129 52652766343115808547389847)
      ·
        refine ⟨78979149514673712821084771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52652766343115808547389847 78979149514673712821084771)
        ·
          refine ⟨118468724272010569231627157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78979149514673712821084771 118468724272010569231627157)
          ·
            refine ⟨5553221450250495432732523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 118468724272010569231627157 5553221450250495432732523)
            ·
              refine ⟨8329832175375743149098785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5553221450250495432732523 8329832175375743149098785)
              ·
                refine ⟨6247374131531807361824089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8329832175375743149098785 6247374131531807361824089)
                ·
                  refine ⟨4685530598648855521368067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6247374131531807361824089 4685530598648855521368067)
                  ·
                    refine ⟨7028295897973283282052101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4685530598648855521368067 7028295897973283282052101)
                    ·
                      refine ⟨1317805480869990615384769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7028295897973283282052101 1317805480869990615384769)
                      ·
                        rfl

theorem cell23_2566417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 4].length) (baseStart_2566417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566417 prefixEnd_2566417 := by exact prefixLift 2566417
  have htrace : WordTrace (prefixWord ++ tailWord_2566417) baseStart_2566417 baseEnd_2566417 := by
    simpa [prefixWord, tailWord_2566417, baseEnd_2566417] using wordTrace_append hprefix tailTrace_2566417
  have hstable : (prefixWord ++ tailWord_2566417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566417).length < 2 ^ (prefixWord ++ tailWord_2566417).sum := by decide
  have hdescent : baseEnd_2566417 < baseStart_2566417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566427 : List Nat := [1, 1, 1, 1, 1, 1, 9, 1, 3, 4]
def baseStart_2566427 : Nat := 118140960795 + 2566427 * 2 ^ 59
def prefixEnd_2566427 : Nat := 4983230072969 + 3 ^ 40 * 2566427 * 2
def baseEnd_2566427 : Nat := 439270205225511858753241

theorem tailTrace_2566427 : CollatzResearch.WordTrace tailWord_2566427 prefixEnd_2566427 439270205225511858753241 := by
  unfold tailWord_2566427
  simp only [CollatzResearch.WordTrace]
  refine ⟨93605282673280764681001535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62403521782187176454001023 93605282673280764681001535)
  ·
    refine ⟨140407924009921147021502303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93605282673280764681001535 140407924009921147021502303)
    ·
      refine ⟨210611886014881720532253455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140407924009921147021502303 210611886014881720532253455)
      ·
        refine ⟨315917829022322580798380183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210611886014881720532253455 315917829022322580798380183)
        ·
          refine ⟨473876743533483871197570275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315917829022322580798380183 473876743533483871197570275)
          ·
            refine ⟨710815115300225806796355413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473876743533483871197570275 710815115300225806796355413)
            ·
              refine ⟨4164932316212260586697395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 710815115300225806796355413 4164932316212260586697395)
              ·
                refine ⟨6247398474318390880046093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4164932316212260586697395 6247398474318390880046093)
                ·
                  refine ⟨2342774427869396580017285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6247398474318390880046093 2342774427869396580017285)
                  ·
                    refine ⟨439270205225511858753241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2342774427869396580017285 439270205225511858753241)
                    ·
                      rfl

theorem cell23_2566427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 3, 4].length) (baseStart_2566427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566427 prefixEnd_2566427 := by exact prefixLift 2566427
  have htrace : WordTrace (prefixWord ++ tailWord_2566427) baseStart_2566427 baseEnd_2566427 := by
    simpa [prefixWord, tailWord_2566427, baseEnd_2566427] using wordTrace_append hprefix tailTrace_2566427
  have hstable : (prefixWord ++ tailWord_2566427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566427).length < 2 ^ (prefixWord ++ tailWord_2566427).sum := by decide
  have hdescent : baseEnd_2566427 < baseStart_2566427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566507 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 2, 6, 2]
def baseStart_2566507 : Nat := 118140960795 + 2566507 * 2 ^ 59
def prefixEnd_2566507 : Nat := 4983230072969 + 3 ^ 40 * 2566507 * 2
def baseEnd_2566507 : Nat := 1317851694128895263259355

theorem tailTrace_2566507 : CollatzResearch.WordTrace tailWord_2566507 prefixEnd_2566507 1317851694128895263259355 := by
  unfold tailWord_2566507
  simp only [CollatzResearch.WordTrace]
  refine ⟨93608200512990938343913775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62405467008660625562609183 93608200512990938343913775)
  ·
    refine ⟨140412300769486407515870663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93608200512990938343913775 140412300769486407515870663)
    ·
      refine ⟨210618451154229611273805995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140412300769486407515870663 210618451154229611273805995)
      ·
        refine ⟨315927676731344416910708993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210618451154229611273805995 315927676731344416910708993)
        ·
          refine ⟨236945757548508312683031745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315927676731344416910708993 236945757548508312683031745)
          ·
            refine ⟨177709318161381234512273809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236945757548508312683031745 177709318161381234512273809)
            ·
              refine ⟨133281988621035925884205357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177709318161381234512273809 133281988621035925884205357)
              ·
                refine ⟨49980745732888472206577009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133281988621035925884205357 49980745732888472206577009)
                ·
                  refine ⟨37485559299666354154932757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49980745732888472206577009 37485559299666354154932757)
                  ·
                    refine ⟨1757135592171860351012473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37485559299666354154932757 1757135592171860351012473)
                    ·
                      refine ⟨1317851694128895263259355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1757135592171860351012473 1317851694128895263259355)
                      ·
                        rfl

theorem cell23_2566507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 6, 2].length) (baseStart_2566507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566507 prefixEnd_2566507 := by exact prefixLift 2566507
  have htrace : WordTrace (prefixWord ++ tailWord_2566507) baseStart_2566507 baseEnd_2566507 := by
    simpa [prefixWord, tailWord_2566507, baseEnd_2566507] using wordTrace_append hprefix tailTrace_2566507
  have hstable : (prefixWord ++ tailWord_2566507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566507).length < 2 ^ (prefixWord ++ tailWord_2566507).sum := by decide
  have hdescent : baseEnd_2566507 < baseStart_2566507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566554 : List Nat := [3, 1, 1, 4, 1, 2, 3, 1, 1, 2, 4]
def baseStart_2566554 : Nat := 118140960795 + 2566554 * 2 ^ 59
def prefixEnd_2566554 : Nat := 4983230072969 + 3 ^ 40 * 2566554 * 2
def baseEnd_2566554 : Nat := 1317875827719656579371639

theorem tailTrace_2566554 : CollatzResearch.WordTrace tailWord_2566554 prefixEnd_2566554 1317875827719656579371639 := by
  unfold tailWord_2566554
  simp only [CollatzResearch.WordTrace]
  refine ⟨23402478685955166342718679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62406609829213776913916477 23402478685955166342718679)
  ·
    refine ⟨35103718028932749514078019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23402478685955166342718679 35103718028932749514078019)
    ·
      refine ⟨52655577043399124271117029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35103718028932749514078019 52655577043399124271117029)
      ·
        refine ⟨9872920695637335800834443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52655577043399124271117029 9872920695637335800834443)
        ·
          refine ⟨14809381043456003701251665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9872920695637335800834443 14809381043456003701251665)
          ·
            refine ⟨11107035782592002775938749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14809381043456003701251665 11107035782592002775938749)
            ·
              refine ⟨4165138418472001040977031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11107035782592002775938749 4165138418472001040977031)
              ·
                refine ⟨6247707627708001561465547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4165138418472001040977031 6247707627708001561465547)
                ·
                  refine ⟨9371561441562002342198321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6247707627708001561465547 9371561441562002342198321)
                  ·
                    refine ⟨7028671081171501756648741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9371561441562002342198321 7028671081171501756648741)
                    ·
                      refine ⟨1317875827719656579371639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7028671081171501756648741 1317875827719656579371639)
                      ·
                        rfl

theorem cell23_2566554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_2566554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566554 prefixEnd_2566554 := by exact prefixLift 2566554
  have htrace : WordTrace (prefixWord ++ tailWord_2566554) baseStart_2566554 baseEnd_2566554 := by
    simpa [prefixWord, tailWord_2566554, baseEnd_2566554] using wordTrace_append hprefix tailTrace_2566554
  have hstable : (prefixWord ++ tailWord_2566554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566554).length < 2 ^ (prefixWord ++ tailWord_2566554).sum := by decide
  have hdescent : baseEnd_2566554 < baseStart_2566554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566558 : List Nat := [4, 3, 1, 2, 1, 2, 2, 2, 1, 1, 4]
def baseStart_2566558 : Nat := 118140960795 + 2566558 * 2 ^ 59
def prefixEnd_2566558 : Nat := 4983230072969 + 3 ^ 40 * 2566558 * 2
def baseEnd_2566558 : Nat := 1317877881642274563721621

theorem tailTrace_2566558 : CollatzResearch.WordTrace tailWord_2566558 prefixEnd_2566558 1317877881642274563721621 := by
  unfold tailWord_2566558
  simp only [CollatzResearch.WordTrace]
  refine ⟨11701257579475771756752541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62406707090537449369346885 11701257579475771756752541)
  ·
    refine ⟨4387971592303414408782203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11701257579475771756752541 4387971592303414408782203)
    ·
      refine ⟨6581957388455121613173305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4387971592303414408782203 6581957388455121613173305)
      ·
        refine ⟨4936468041341341209879979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6581957388455121613173305 4936468041341341209879979)
        ·
          refine ⟨7404702062012011814819969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4936468041341341209879979 7404702062012011814819969)
          ·
            refine ⟨5553526546509008861114977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7404702062012011814819969 5553526546509008861114977)
            ·
              refine ⟨4165144909881756645836233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5553526546509008861114977 4165144909881756645836233)
              ·
                refine ⟨3123858682411317484377175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4165144909881756645836233 3123858682411317484377175)
                ·
                  refine ⟨4685788023616976226565763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3123858682411317484377175 4685788023616976226565763)
                  ·
                    refine ⟨7028682035425464339848645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4685788023616976226565763 7028682035425464339848645)
                    ·
                      refine ⟨1317877881642274563721621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7028682035425464339848645 1317877881642274563721621)
                      ·
                        rfl

theorem cell23_2566558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_2566558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566558 prefixEnd_2566558 := by exact prefixLift 2566558
  have htrace : WordTrace (prefixWord ++ tailWord_2566558) baseStart_2566558 baseEnd_2566558 := by
    simpa [prefixWord, tailWord_2566558, baseEnd_2566558] using wordTrace_append hprefix tailTrace_2566558
  have hstable : (prefixWord ++ tailWord_2566558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566558).length < 2 ^ (prefixWord ++ tailWord_2566558).sum := by decide
  have hdescent : baseEnd_2566558 < baseStart_2566558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566584 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 5, 3, 2]
def baseStart_2566584 : Nat := 118140960795 + 2566584 * 2 ^ 59
def prefixEnd_2566584 : Nat := 4983230072969 + 3 ^ 40 * 2566584 * 2
def baseEnd_2566584 : Nat := 1317891232139291461996501

theorem tailTrace_2566584 : CollatzResearch.WordTrace tailWord_2566584 prefixEnd_2566584 1317891232139291461996501 := by
  unfold tailWord_2566584
  simp only [CollatzResearch.WordTrace]
  refine ⟨46805504466855990247233403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62407339289141320329644537 46805504466855990247233403)
  ·
    refine ⟨70208256700283985370850105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46805504466855990247233403 70208256700283985370850105)
    ·
      refine ⟨52656192525212989028137579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70208256700283985370850105 52656192525212989028137579)
      ·
        refine ⟨78984288787819483542206369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52656192525212989028137579 78984288787819483542206369)
        ·
          refine ⟨59238216590864612656654777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78984288787819483542206369 59238216590864612656654777)
          ·
            refine ⟨44428662443148459492491083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59238216590864612656654777 44428662443148459492491083)
            ·
              refine ⟨66642993664722689238736625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44428662443148459492491083 66642993664722689238736625)
              ·
                refine ⟨49982245248542016929052469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66642993664722689238736625 49982245248542016929052469)
                ·
                  refine ⟨4685835492050814087098669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49982245248542016929052469 4685835492050814087098669)
                  ·
                    refine ⟨1757188309519055282662001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4685835492050814087098669 1757188309519055282662001)
                    ·
                      refine ⟨1317891232139291461996501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1757188309519055282662001 1317891232139291461996501)
                      ·
                        rfl

theorem cell23_2566584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 5, 3, 2].length) (baseStart_2566584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566584 prefixEnd_2566584 := by exact prefixLift 2566584
  have htrace : WordTrace (prefixWord ++ tailWord_2566584) baseStart_2566584 baseEnd_2566584 := by
    simpa [prefixWord, tailWord_2566584, baseEnd_2566584] using wordTrace_append hprefix tailTrace_2566584
  have hstable : (prefixWord ++ tailWord_2566584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566584).length < 2 ^ (prefixWord ++ tailWord_2566584).sum := by decide
  have hdescent : baseEnd_2566584 < baseStart_2566584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566617 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 4, 1, 5]
def baseStart_2566617 : Nat := 118140960795 + 2566617 * 2 ^ 59
def prefixEnd_2566617 : Nat := 4983230072969 + 3 ^ 40 * 2566617 * 2
def baseEnd_2566617 : Nat := 1317908177000889832883849

theorem tailTrace_2566617 : CollatzResearch.WordTrace tailWord_2566617 prefixEnd_2566617 1317908177000889832883849 := by
  unfold tailWord_2566617
  simp only [CollatzResearch.WordTrace]
  refine ⟨93612212542592427130418105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62408141695061618086945403 93612212542592427130418105)
  ·
    refine ⟨70209159406944320347813579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93612212542592427130418105 70209159406944320347813579)
    ·
      refine ⟨105313739110416480521720369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70209159406944320347813579 105313739110416480521720369)
      ·
        refine ⟨78985304332812360391290277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105313739110416480521720369 78985304332812360391290277)
        ·
          refine ⟨14809744562402317573366927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78985304332812360391290277 14809744562402317573366927)
          ·
            refine ⟨22214616843603476360050391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14809744562402317573366927 22214616843603476360050391)
            ·
              refine ⟨33321925265405214540075587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22214616843603476360050391 33321925265405214540075587)
              ·
                refine ⟨49982887898107821810113381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33321925265405214540075587 49982887898107821810113381)
                ·
                  refine ⟨9371791480895216589396259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49982887898107821810113381 9371791480895216589396259)
                  ·
                    refine ⟨14057687221342824884094389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9371791480895216589396259 14057687221342824884094389)
                    ·
                      refine ⟨1317908177000889832883849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14057687221342824884094389 1317908177000889832883849)
                      ·
                        rfl

theorem cell23_2566617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_2566617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566617 prefixEnd_2566617 := by exact prefixLift 2566617
  have htrace : WordTrace (prefixWord ++ tailWord_2566617) baseStart_2566617 baseEnd_2566617 := by
    simpa [prefixWord, tailWord_2566617, baseEnd_2566617] using wordTrace_append hprefix tailTrace_2566617
  have hstable : (prefixWord ++ tailWord_2566617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566617).length < 2 ^ (prefixWord ++ tailWord_2566617).sum := by decide
  have hdescent : baseEnd_2566617 < baseStart_2566617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566631 : List Nat := [1, 1, 5, 2, 1, 1, 3, 2, 1, 4, 2]
def baseStart_2566631 : Nat := 118140960795 + 2566631 * 2 ^ 59
def prefixEnd_2566631 : Nat := 4983230072969 + 3 ^ 40 * 2566631 * 2
def baseEnd_2566631 : Nat := 1317915365730052778108785

theorem tailTrace_2566631 : CollatzResearch.WordTrace tailWord_2566631 prefixEnd_2566631 1317915365730052778108785 := by
  unfold tailWord_2566631
  simp only [CollatzResearch.WordTrace]
  refine ⟨93612723164541707521427747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62408482109694471680951831 93612723164541707521427747)
  ·
    refine ⟨140419084746812561282141621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93612723164541707521427747 140419084746812561282141621)
    ·
      refine ⟨13164289195013677620200777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 140419084746812561282141621 13164289195013677620200777)
      ·
        refine ⟨9873216896260258215150583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13164289195013677620200777 9873216896260258215150583)
        ·
          refine ⟨14809825344390387322725875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9873216896260258215150583 14809825344390387322725875)
          ·
            refine ⟨22214738016585580984088813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14809825344390387322725875 22214738016585580984088813)
            ·
              refine ⟨8330526756219592869033305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22214738016585580984088813 8330526756219592869033305)
              ·
                refine ⟨6247895067164694651774979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8330526756219592869033305 6247895067164694651774979)
                ·
                  refine ⟨9371842600747041977662469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6247895067164694651774979 9371842600747041977662469)
                  ·
                    refine ⟨1757220487640070370811713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9371842600747041977662469 1757220487640070370811713)
                    ·
                      refine ⟨1317915365730052778108785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1757220487640070370811713 1317915365730052778108785)
                      ·
                        rfl

theorem cell23_2566631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_2566631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566631 prefixEnd_2566631 := by exact prefixLift 2566631
  have htrace : WordTrace (prefixWord ++ tailWord_2566631) baseStart_2566631 baseEnd_2566631 := by
    simpa [prefixWord, tailWord_2566631, baseEnd_2566631] using wordTrace_append hprefix tailTrace_2566631
  have hstable : (prefixWord ++ tailWord_2566631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566631).length < 2 ^ (prefixWord ++ tailWord_2566631).sum := by decide
  have hdescent : baseEnd_2566631 < baseStart_2566631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566634 : List Nat := [3, 1, 3, 1, 3, 1, 2, 1, 2, 1, 5]
def baseStart_2566634 : Nat := 118140960795 + 2566634 * 2 ^ 59
def prefixEnd_2566634 : Nat := 4983230072969 + 3 ^ 40 * 2566634 * 2
def baseEnd_2566634 : Nat := 1317916906172016266371271

theorem tailTrace_2566634 : CollatzResearch.WordTrace tailWord_2566634 prefixEnd_2566634 1317916906172016266371271 := by
  unfold tailWord_2566634
  simp only [CollatzResearch.WordTrace]
  refine ⟨23403208145882709758446739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62408555055687226022524637 23403208145882709758446739)
  ·
    refine ⟨35104812218824064637670109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23403208145882709758446739 35104812218824064637670109)
    ·
      refine ⟨13164304582059024239126291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35104812218824064637670109 13164304582059024239126291)
      ·
        refine ⟨19746456873088536358689437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13164304582059024239126291 19746456873088536358689437)
        ·
          refine ⟨7404921327408201134508539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19746456873088536358689437 7404921327408201134508539)
          ·
            refine ⟨11107381991112301701762809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7404921327408201134508539 11107381991112301701762809)
            ·
              refine ⟨8330536493334226276322107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11107381991112301701762809 8330536493334226276322107)
              ·
                refine ⟨12495804740001339414483161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8330536493334226276322107 12495804740001339414483161)
                ·
                  refine ⟨9371853555001004560862371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12495804740001339414483161 9371853555001004560862371)
                  ·
                    refine ⟨14057780332501506841293557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9371853555001004560862371 14057780332501506841293557)
                    ·
                      refine ⟨1317916906172016266371271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14057780332501506841293557 1317916906172016266371271)
                      ·
                        rfl

theorem cell23_2566634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_2566634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566634 prefixEnd_2566634 := by exact prefixLift 2566634
  have htrace : WordTrace (prefixWord ++ tailWord_2566634) baseStart_2566634 baseEnd_2566634 := by
    simpa [prefixWord, tailWord_2566634, baseEnd_2566634] using wordTrace_append hprefix tailTrace_2566634
  have hstable : (prefixWord ++ tailWord_2566634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566634).length < 2 ^ (prefixWord ++ tailWord_2566634).sum := by decide
  have hdescent : baseEnd_2566634 < baseStart_2566634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566648 : List Nat := [2, 1, 2, 1, 1, 4, 4, 2, 2, 2, 2]
def baseStart_2566648 : Nat := 118140960795 + 2566648 * 2 ^ 59
def prefixEnd_2566648 : Nat := 4983230072969 + 3 ^ 40 * 2566648 * 2
def baseEnd_2566648 : Nat := 1317924094901179211596207

theorem tailTrace_2566648 : CollatzResearch.WordTrace tailWord_2566648 prefixEnd_2566648 1317924094901179211596207 := by
  unfold tailWord_2566648
  simp only [CollatzResearch.WordTrace]
  refine ⟨46806671602740059712398299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62408895470320079616531065 46806671602740059712398299)
  ·
    refine ⟨70210007404110089568597449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46806671602740059712398299 70210007404110089568597449)
    ·
      refine ⟨52657505553082567176448087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70210007404110089568597449 52657505553082567176448087)
      ·
        refine ⟨78986258329623850764672131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52657505553082567176448087 78986258329623850764672131)
        ·
          refine ⟨118479387494435776147008197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78986258329623850764672131 118479387494435776147008197)
          ·
            refine ⟨22214885155206708027564037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118479387494435776147008197 22214885155206708027564037)
            ·
              refine ⟨4165290966601257755168257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22214885155206708027564037 4165290966601257755168257)
              ·
                refine ⟨3123968224950943316376193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4165290966601257755168257 3123968224950943316376193)
                ·
                  refine ⟨2342976168713207487282145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3123968224950943316376193 2342976168713207487282145)
                  ·
                    refine ⟨1757232126534905615461609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2342976168713207487282145 1757232126534905615461609)
                    ·
                      refine ⟨1317924094901179211596207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1757232126534905615461609 1317924094901179211596207)
                      ·
                        rfl

theorem cell23_2566648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 2, 2, 2].length) (baseStart_2566648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566648 prefixEnd_2566648 := by exact prefixLift 2566648
  have htrace : WordTrace (prefixWord ++ tailWord_2566648) baseStart_2566648 baseEnd_2566648 := by
    simpa [prefixWord, tailWord_2566648, baseEnd_2566648] using wordTrace_append hprefix tailTrace_2566648
  have hstable : (prefixWord ++ tailWord_2566648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566648).length < 2 ^ (prefixWord ++ tailWord_2566648).sum := by decide
  have hdescent : baseEnd_2566648 < baseStart_2566648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566684 : List Nat := [2, 2, 3, 1, 2, 3, 1, 1, 1, 7]
def baseStart_2566684 : Nat := 118140960795 + 2566684 * 2 ^ 59
def prefixEnd_2566684 : Nat := 4983230072969 + 3 ^ 40 * 2566684 * 2
def baseEnd_2566684 : Nat := 439314193401580356915347

theorem tailTrace_2566684 : CollatzResearch.WordTrace tailWord_2566684 prefixEnd_2566684 439314193401580356915347 := by
  unfold tailWord_2566684
  simp only [CollatzResearch.WordTrace]
  refine ⟨46807328116674848786553553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62409770822233131715404737 46807328116674848786553553)
  ·
    refine ⟨35105496087506136589915165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46807328116674848786553553 35105496087506136589915165)
    ·
      refine ⟨13164561032814801221218187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35105496087506136589915165 13164561032814801221218187)
      ·
        refine ⟨19746841549222201831827281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13164561032814801221218187 19746841549222201831827281)
        ·
          refine ⟨14810131161916651373870461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19746841549222201831827281 14810131161916651373870461)
          ·
            refine ⟨5553799185718744265201423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14810131161916651373870461 5553799185718744265201423)
            ·
              refine ⟨8330698778578116397802135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5553799185718744265201423 8330698778578116397802135)
              ·
                refine ⟨12496048167867174596703203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8330698778578116397802135 12496048167867174596703203)
                ·
                  refine ⟨18744072251800761895054805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12496048167867174596703203 18744072251800761895054805)
                  ·
                    refine ⟨439314193401580356915347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18744072251800761895054805 439314193401580356915347)
                    ·
                      rfl

theorem cell23_2566684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_2566684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566684 prefixEnd_2566684 := by exact prefixLift 2566684
  have htrace : WordTrace (prefixWord ++ tailWord_2566684) baseStart_2566684 baseEnd_2566684 := by
    simpa [prefixWord, tailWord_2566684, baseEnd_2566684] using wordTrace_append hprefix tailTrace_2566684
  have hstable : (prefixWord ++ tailWord_2566684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566684).length < 2 ^ (prefixWord ++ tailWord_2566684).sum := by decide
  have hdescent : baseEnd_2566684 < baseStart_2566684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566688 : List Nat := [2, 1, 1, 6, 2, 1, 2, 3, 5]
def baseStart_2566688 : Nat := 118140960795 + 2566688 * 2 ^ 59
def prefixEnd_2566688 : Nat := 4983230072969 + 3 ^ 40 * 2566688 * 2
def baseEnd_2566688 : Nat := 146438292680817672788447

theorem tailTrace_2566688 : CollatzResearch.WordTrace tailWord_2566688 prefixEnd_2566688 146438292680817672788447 := by
  unfold tailWord_2566688
  simp only [CollatzResearch.WordTrace]
  refine ⟨46807401062667603128126359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62409868083556804170835145 46807401062667603128126359)
  ·
    refine ⟨70211101594001404692189539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46807401062667603128126359 70211101594001404692189539)
    ·
      refine ⟨105316652391002107038284309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70211101594001404692189539 105316652391002107038284309)
      ·
        refine ⟨4936718080828223767419577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 105316652391002107038284309 4936718080828223767419577)
        ·
          refine ⟨3702538560621167825564683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4936718080828223767419577 3702538560621167825564683)
          ·
            refine ⟨5553807840931751738347025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3702538560621167825564683 5553807840931751738347025)
            ·
              refine ⟨4165355880698813803760269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5553807840931751738347025 4165355880698813803760269)
              ·
                refine ⟨1562008455262055176410101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4165355880698813803760269 1562008455262055176410101)
                ·
                  refine ⟨146438292680817672788447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1562008455262055176410101 146438292680817672788447)
                  ·
                    rfl

theorem cell23_2566688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 3, 5].length) (baseStart_2566688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566688 prefixEnd_2566688 := by exact prefixLift 2566688
  have htrace : WordTrace (prefixWord ++ tailWord_2566688) baseStart_2566688 baseEnd_2566688 := by
    simpa [prefixWord, tailWord_2566688, baseEnd_2566688] using wordTrace_append hprefix tailTrace_2566688
  have hstable : (prefixWord ++ tailWord_2566688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566688).length < 2 ^ (prefixWord ++ tailWord_2566688).sum := by decide
  have hdescent : baseEnd_2566688 < baseStart_2566688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566704 : List Nat := [2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 4]
def baseStart_2566704 : Nat := 118140960795 + 2566704 * 2 ^ 59
def prefixEnd_2566704 : Nat := 4983230072969 + 3 ^ 40 * 2566704 * 2
def baseEnd_2566704 : Nat := 1317952849817830992495949

theorem tailTrace_2566704 : CollatzResearch.WordTrace tailWord_2566704 prefixEnd_2566704 1317952849817830992495949 := by
  unfold tailWord_2566704
  simp only [CollatzResearch.WordTrace]
  refine ⟨46807692846638620494417583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62410257128851493992556777 46807692846638620494417583)
  ·
    refine ⟨70211539269957930741626375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46807692846638620494417583 70211539269957930741626375)
    ·
      refine ⟨105317308904936896112439563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70211539269957930741626375 105317308904936896112439563)
      ·
        refine ⟨157975963357405344168659345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105317308904936896112439563 157975963357405344168659345)
        ·
          refine ⟨118481972518054008126494509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157975963357405344168659345 118481972518054008126494509)
          ·
            refine ⟨44430739694270253047435441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118481972518054008126494509 44430739694270253047435441)
            ·
              refine ⟨33323054770702689785576581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44430739694270253047435441 33323054770702689785576581)
              ·
                refine ⟨6248072769506754334795609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33323054770702689785576581 6248072769506754334795609)
                ·
                  refine ⟨4686054577130065751096707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6248072769506754334795609 4686054577130065751096707)
                  ·
                    refine ⟨7029081865695098626645061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4686054577130065751096707 7029081865695098626645061)
                    ·
                      refine ⟨1317952849817830992495949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7029081865695098626645061 1317952849817830992495949)
                      ·
                        rfl

theorem cell23_2566704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 4].length) (baseStart_2566704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566704 prefixEnd_2566704 := by exact prefixLift 2566704
  have htrace : WordTrace (prefixWord ++ tailWord_2566704) baseStart_2566704 baseEnd_2566704 := by
    simpa [prefixWord, tailWord_2566704, baseEnd_2566704] using wordTrace_append hprefix tailTrace_2566704
  have hstable : (prefixWord ++ tailWord_2566704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566704).length < 2 ^ (prefixWord ++ tailWord_2566704).sum := by decide
  have hdescent : baseEnd_2566704 < baseStart_2566704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566747 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 6]
def baseStart_2566747 : Nat := 118140960795 + 2566747 * 2 ^ 59
def prefixEnd_2566747 : Nat := 4983230072969 + 3 ^ 40 * 2566747 * 2
def baseEnd_2566747 : Nat := 1317974929485974324258251

theorem tailTrace_2566747 : CollatzResearch.WordTrace tailWord_2566747 prefixEnd_2566747 1317974929485974324258251 := by
  unfold tailWord_2566747
  simp only [CollatzResearch.WordTrace]
  refine ⟨93616954032121459332650495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62411302688080972888433663 93616954032121459332650495)
  ·
    refine ⟨140425431048182188998975743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93616954032121459332650495 140425431048182188998975743)
    ·
      refine ⟨210638146572273283498463615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140425431048182188998975743 210638146572273283498463615)
      ·
        refine ⟨315957219858409925247695423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210638146572273283498463615 315957219858409925247695423)
        ·
          refine ⟨473935829787614887871543135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315957219858409925247695423 473935829787614887871543135)
          ·
            refine ⟨710903744681422331807314703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473935829787614887871543135 710903744681422331807314703)
            ·
              refine ⟨1066355617022133497710972055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 710903744681422331807314703 1066355617022133497710972055)
              ·
                refine ⟨1599533425533200246566458083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1066355617022133497710972055 1599533425533200246566458083)
                ·
                  refine ⟨2399300138299800369849687125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1599533425533200246566458083 2399300138299800369849687125)
                  ·
                    refine ⟨28116798495700785584176021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2399300138299800369849687125 28116798495700785584176021)
                    ·
                      refine ⟨1317974929485974324258251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28116798495700785584176021 1317974929485974324258251)
                      ·
                        rfl

theorem cell23_2566747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 6].length) (baseStart_2566747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566747 prefixEnd_2566747 := by exact prefixLift 2566747
  have htrace : WordTrace (prefixWord ++ tailWord_2566747) baseStart_2566747 baseEnd_2566747 := by
    simpa [prefixWord, tailWord_2566747, baseEnd_2566747] using wordTrace_append hprefix tailTrace_2566747
  have hstable : (prefixWord ++ tailWord_2566747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566747).length < 2 ^ (prefixWord ++ tailWord_2566747).sum := by decide
  have hdescent : baseEnd_2566747 < baseStart_2566747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566771 : List Nat := [1, 1, 1, 2, 2, 1, 1, 7, 3, 1, 3]
def baseStart_2566771 : Nat := 118140960795 + 2566771 * 2 ^ 59
def prefixEnd_2566771 : Nat := 4983230072969 + 3 ^ 40 * 2566771 * 2
def baseEnd_2566771 : Nat := 1317987253021682230358141

theorem tailTrace_2566771 : CollatzResearch.WordTrace tailWord_2566771 prefixEnd_2566771 1317987253021682230358141 := by
  unfold tailWord_2566771
  simp only [CollatzResearch.WordTrace]
  refine ⟨93617829384034511431524167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62411886256023007621016111 93617829384034511431524167)
  ·
    refine ⟨140426744076051767147286251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93617829384034511431524167 140426744076051767147286251)
    ·
      refine ⟨210640116114077650720929377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140426744076051767147286251 210640116114077650720929377)
      ·
        refine ⟨157980087085558238040697033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210640116114077650720929377 157980087085558238040697033)
        ·
          refine ⟨118485065314168678530522775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157980087085558238040697033 118485065314168678530522775)
          ·
            refine ⟨177727597971253017795784163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118485065314168678530522775 177727597971253017795784163)
            ·
              refine ⟨266591396956879526693676245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177727597971253017795784163 266591396956879526693676245)
              ·
                refine ⟨6248235866176863906883037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 266591396956879526693676245 6248235866176863906883037)
                ·
                  refine ⟨2343088449816323965081139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6248235866176863906883037 2343088449816323965081139)
                  ·
                    refine ⟨3514632674724485947621709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2343088449816323965081139 3514632674724485947621709)
                    ·
                      refine ⟨1317987253021682230358141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3514632674724485947621709 1317987253021682230358141)
                      ·
                        rfl

theorem cell23_2566771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 3, 1, 3].length) (baseStart_2566771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566771 prefixEnd_2566771 := by exact prefixLift 2566771
  have htrace : WordTrace (prefixWord ++ tailWord_2566771) baseStart_2566771 baseEnd_2566771 := by
    simpa [prefixWord, tailWord_2566771, baseEnd_2566771] using wordTrace_append hprefix tailTrace_2566771
  have hstable : (prefixWord ++ tailWord_2566771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566771).length < 2 ^ (prefixWord ++ tailWord_2566771).sum := by decide
  have hdescent : baseEnd_2566771 < baseStart_2566771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566808 : List Nat := [2, 1, 2, 4, 1, 1, 5, 1, 1, 5]
def baseStart_2566808 : Nat := 118140960795 + 2566808 * 2 ^ 59
def prefixEnd_2566808 : Nat := 4983230072969 + 3 ^ 40 * 2566808 * 2
def baseEnd_2566808 : Nat := 439335417268632861865157

theorem tailTrace_2566808 : CollatzResearch.WordTrace tailWord_2566808 prefixEnd_2566808 439335417268632861865157 := by
  unfold tailWord_2566808
  simp only [CollatzResearch.WordTrace]
  refine ⟨46809589442450233375310539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62412785923266977833747385 46809589442450233375310539)
  ·
    refine ⟨70214384163675350062965809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46809589442450233375310539 70214384163675350062965809)
    ·
      refine ⟨52660788122756512547224357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70214384163675350062965809 52660788122756512547224357)
      ·
        refine ⟨9873897773016846102604567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52660788122756512547224357 9873897773016846102604567)
        ·
          refine ⟨14810846659525269153906851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9873897773016846102604567 14810846659525269153906851)
          ·
            refine ⟨22216269989287903730860277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14810846659525269153906851 22216269989287903730860277)
            ·
              refine ⟨2082775311495740974768151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22216269989287903730860277 2082775311495740974768151)
              ·
                refine ⟨3124162967243611462152227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2082775311495740974768151 3124162967243611462152227)
                ·
                  refine ⟨4686244450865417193228341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3124162967243611462152227 4686244450865417193228341)
                  ·
                    refine ⟨439335417268632861865157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4686244450865417193228341 439335417268632861865157)
                    ·
                      rfl

theorem cell23_2566808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 1, 5].length) (baseStart_2566808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566808 prefixEnd_2566808 := by exact prefixLift 2566808
  have htrace : WordTrace (prefixWord ++ tailWord_2566808) baseStart_2566808 baseEnd_2566808 := by
    simpa [prefixWord, tailWord_2566808, baseEnd_2566808] using wordTrace_append hprefix tailTrace_2566808
  have hstable : (prefixWord ++ tailWord_2566808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566808).length < 2 ^ (prefixWord ++ tailWord_2566808).sum := by decide
  have hdescent : baseEnd_2566808 < baseStart_2566808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566831 : List Nat := [1, 1, 2, 1, 2, 5, 1, 2, 3, 2, 3]
def baseStart_2566831 : Nat := 118140960795 + 2566831 * 2 ^ 59
def prefixEnd_2566831 : Nat := 4983230072969 + 3 ^ 40 * 2566831 * 2
def baseEnd_2566831 : Nat := 1318018061860951995607865

theorem tailTrace_2566831 : CollatzResearch.WordTrace tailWord_2566831 prefixEnd_2566831 1318018061860951995607865 := by
  unfold tailWord_2566831
  simp only [CollatzResearch.WordTrace]
  refine ⟨93620017763817141678708347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62413345175878094452472231 93620017763817141678708347)
  ·
    refine ⟨140430026645725712518062521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93620017763817141678708347 140430026645725712518062521)
    ·
      refine ⟨105322519984294284388546891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140430026645725712518062521 105322519984294284388546891)
      ·
        refine ⟨157983779976441426582820337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105322519984294284388546891 157983779976441426582820337)
        ·
          refine ⟨118487834982331069937115253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157983779976441426582820337 118487834982331069937115253)
          ·
            refine ⟨11108234529593537806604555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 118487834982331069937115253 11108234529593537806604555)
            ·
              refine ⟨16662351794390306709906833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11108234529593537806604555 16662351794390306709906833)
              ·
                refine ⟨12496763845792730032430125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16662351794390306709906833 12496763845792730032430125)
                ·
                  refine ⟨4686286442172273762161297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12496763845792730032430125 4686286442172273762161297)
                  ·
                    refine ⟨3514714831629205321620973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4686286442172273762161297 3514714831629205321620973)
                    ·
                      refine ⟨1318018061860951995607865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3514714831629205321620973 1318018061860951995607865)
                      ·
                        rfl

theorem cell23_2566831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 2, 3].length) (baseStart_2566831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566831 prefixEnd_2566831 := by exact prefixLift 2566831
  have htrace : WordTrace (prefixWord ++ tailWord_2566831) baseStart_2566831 baseEnd_2566831 := by
    simpa [prefixWord, tailWord_2566831, baseEnd_2566831] using wordTrace_append hprefix tailTrace_2566831
  have hstable : (prefixWord ++ tailWord_2566831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566831).length < 2 ^ (prefixWord ++ tailWord_2566831).sum := by decide
  have hdescent : baseEnd_2566831 < baseStart_2566831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566845 : List Nat := [1, 4, 1, 2, 1, 4, 1, 2, 3, 2, 2]
def baseStart_2566845 : Nat := 118140960795 + 2566845 * 2 ^ 59
def prefixEnd_2566845 : Nat := 4983230072969 + 3 ^ 40 * 2566845 * 2
def baseEnd_2566845 : Nat := 1318025250590114940832801

theorem tailTrace_2566845 : CollatzResearch.WordTrace tailWord_2566845 prefixEnd_2566845 1318025250590114940832801 := by
  unfold tailWord_2566845
  simp only [CollatzResearch.WordTrace]
  refine ⟨93620528385766422069717989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62413685590510948046478659 93620528385766422069717989)
  ·
    refine ⟨17553849072331204138072123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93620528385766422069717989 17553849072331204138072123)
    ·
      refine ⟨26330773608496806207108185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17553849072331204138072123 26330773608496806207108185)
      ·
        refine ⟨19748080206372604655331139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26330773608496806207108185 19748080206372604655331139)
        ·
          refine ⟨29622120309558906982996709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19748080206372604655331139 29622120309558906982996709)
          ·
            refine ⟨5554147558042295059311883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29622120309558906982996709 5554147558042295059311883)
            ·
              refine ⟨8331221337063442588967825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5554147558042295059311883 8331221337063442588967825)
              ·
                refine ⟨6248416002797581941725869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8331221337063442588967825 6248416002797581941725869)
                ·
                  refine ⟨2343156001049093228147201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6248416002797581941725869 2343156001049093228147201)
                  ·
                    refine ⟨1757367000786819921110401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2343156001049093228147201 1757367000786819921110401)
                    ·
                      refine ⟨1318025250590114940832801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1757367000786819921110401 1318025250590114940832801)
                      ·
                        rfl

theorem cell23_2566845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_2566845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566845 prefixEnd_2566845 := by exact prefixLift 2566845
  have htrace : WordTrace (prefixWord ++ tailWord_2566845) baseStart_2566845 baseEnd_2566845 := by
    simpa [prefixWord, tailWord_2566845, baseEnd_2566845] using wordTrace_append hprefix tailTrace_2566845
  have hstable : (prefixWord ++ tailWord_2566845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566845).length < 2 ^ (prefixWord ++ tailWord_2566845).sum := by decide
  have hdescent : baseEnd_2566845 < baseStart_2566845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566849 : List Nat := [1, 2, 6, 2, 1, 2, 1, 1, 2, 3, 2]
def baseStart_2566849 : Nat := 118140960795 + 2566849 * 2 ^ 59
def prefixEnd_2566849 : Nat := 4983230072969 + 3 ^ 40 * 2566849 * 2
def baseEnd_2566849 : Nat := 1318027304512732925182783

theorem tailTrace_2566849 : CollatzResearch.WordTrace tailWord_2566849 prefixEnd_2566849 1318027304512732925182783 := by
  unfold tailWord_2566849
  simp only [CollatzResearch.WordTrace]
  refine ⟨93620674277751930752863601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62413782851834620501909067 93620674277751930752863601)
  ·
    refine ⟨70215505708313948064647701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93620674277751930752863601 70215505708313948064647701)
    ·
      refine ⟨3291351830077216315530361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 70215505708313948064647701 3291351830077216315530361)
      ·
        refine ⟨2468513872557912236647771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3291351830077216315530361 2468513872557912236647771)
        ·
          refine ⟨3702770808836868354971657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2468513872557912236647771 3702770808836868354971657)
          ·
            refine ⟨2777078106627651266228743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3702770808836868354971657 2777078106627651266228743)
            ·
              refine ⟨4165617159941476899343115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2777078106627651266228743 4165617159941476899343115)
              ·
                refine ⟨6248425739912215349014673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4165617159941476899343115 6248425739912215349014673)
                ·
                  refine ⟨4686319304934161511761005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6248425739912215349014673 4686319304934161511761005)
                  ·
                    refine ⟨1757369739350310566910377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4686319304934161511761005 1757369739350310566910377)
                    ·
                      refine ⟨1318027304512732925182783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1757369739350310566910377 1318027304512732925182783)
                      ·
                        rfl

theorem cell23_2566849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_2566849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566849 prefixEnd_2566849 := by exact prefixLift 2566849
  have htrace : WordTrace (prefixWord ++ tailWord_2566849) baseStart_2566849 baseEnd_2566849 := by
    simpa [prefixWord, tailWord_2566849, baseEnd_2566849] using wordTrace_append hprefix tailTrace_2566849
  have hstable : (prefixWord ++ tailWord_2566849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566849).length < 2 ^ (prefixWord ++ tailWord_2566849).sum := by decide
  have hdescent : baseEnd_2566849 < baseStart_2566849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566862 : List Nat := [4, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2]
def baseStart_2566862 : Nat := 118140960795 + 2566862 * 2 ^ 59
def prefixEnd_2566862 : Nat := 4983230072969 + 3 ^ 40 * 2566862 * 2
def baseEnd_2566862 : Nat := 1318033979761241374320223

theorem tailTrace_2566862 : CollatzResearch.WordTrace tailWord_2566862 prefixEnd_2566862 1318033979761241374320223 := by
  unfold tailWord_2566862
  simp only [CollatzResearch.WordTrace]
  refine ⟨11702643553338104246635855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62414098951136555982057893 11702643553338104246635855)
  ·
    refine ⟨17553965330007156369953783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11702643553338104246635855 17553965330007156369953783)
    ·
      refine ⟨26330947995010734554930675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17553965330007156369953783 26330947995010734554930675)
      ·
        refine ⟨39496421992516101832396013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26330947995010734554930675 39496421992516101832396013)
        ·
          refine ⟨14811158247193538187148505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39496421992516101832396013 14811158247193538187148505)
          ·
            refine ⟨11108368685395153640361379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14811158247193538187148505 11108368685395153640361379)
            ·
              refine ⟨16662553028092730460542069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11108368685395153640361379 16662553028092730460542069)
              ·
                refine ⟨1562114346383693480675819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16662553028092730460542069 1562114346383693480675819)
                ·
                  refine ⟨2343171519575540221013729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1562114346383693480675819 2343171519575540221013729)
                  ·
                    refine ⟨1757378639681655165760297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2343171519575540221013729 1757378639681655165760297)
                    ·
                      refine ⟨1318033979761241374320223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1757378639681655165760297 1318033979761241374320223)
                      ·
                        rfl

theorem cell23_2566862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2].length) (baseStart_2566862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566862 prefixEnd_2566862 := by exact prefixLift 2566862
  have htrace : WordTrace (prefixWord ++ tailWord_2566862) baseStart_2566862 baseEnd_2566862 := by
    simpa [prefixWord, tailWord_2566862, baseEnd_2566862] using wordTrace_append hprefix tailTrace_2566862
  have hstable : (prefixWord ++ tailWord_2566862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566862).length < 2 ^ (prefixWord ++ tailWord_2566862).sum := by decide
  have hdescent : baseEnd_2566862 < baseStart_2566862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566952 : List Nat := [2, 1, 5, 1, 1, 1, 3, 3, 2, 2, 2]
def baseStart_2566952 : Nat := 118140960795 + 2566952 * 2 ^ 59
def prefixEnd_2566952 : Nat := 4983230072969 + 3 ^ 40 * 2566952 * 2
def baseEnd_2566952 : Nat := 1318080193020146022194809

theorem tailTrace_2566952 : CollatzResearch.WordTrace tailWord_2566952 prefixEnd_2566952 1318080193020146022194809 := by
  unfold tailWord_2566952
  simp only [CollatzResearch.WordTrace]
  refine ⟨46812215498189389671931555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62416287330919186229242073 46812215498189389671931555)
  ·
    refine ⟨70218323247284084507897333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46812215498189389671931555 70218323247284084507897333)
    ·
      refine ⟨6582967804432882922615375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70218323247284084507897333 6582967804432882922615375)
      ·
        refine ⟨9874451706649324383923063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6582967804432882922615375 9874451706649324383923063)
        ·
          refine ⟨14811677559973986575884595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9874451706649324383923063 14811677559973986575884595)
          ·
            refine ⟨22217516339960979863826893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14811677559973986575884595 22217516339960979863826893)
            ·
              refine ⟨8331568627485367448935085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22217516339960979863826893 8331568627485367448935085)
              ·
                refine ⟨3124338235307012793350657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8331568627485367448935085 3124338235307012793350657)
                ·
                  refine ⟨2343253676480259595012993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3124338235307012793350657 2343253676480259595012993)
                  ·
                    refine ⟨1757440257360194696259745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2343253676480259595012993 1757440257360194696259745)
                    ·
                      refine ⟨1318080193020146022194809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1757440257360194696259745 1318080193020146022194809)
                      ·
                        rfl

theorem cell23_2566952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_2566952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566952 prefixEnd_2566952 := by exact prefixLift 2566952
  have htrace : WordTrace (prefixWord ++ tailWord_2566952) baseStart_2566952 baseEnd_2566952 := by
    simpa [prefixWord, tailWord_2566952, baseEnd_2566952] using wordTrace_append hprefix tailTrace_2566952
  have hstable : (prefixWord ++ tailWord_2566952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566952).length < 2 ^ (prefixWord ++ tailWord_2566952).sum := by decide
  have hdescent : baseEnd_2566952 < baseStart_2566952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2566988 : List Nat := [2, 2, 1, 3, 3, 1, 2, 2, 2, 5]
def baseStart_2566988 : Nat := 118140960795 + 2566988 * 2 ^ 59
def prefixEnd_2566988 : Nat := 4983230072969 + 3 ^ 40 * 2566988 * 2
def baseEnd_2566988 : Nat := 439366226107902627114881

theorem tailTrace_2566988 : CollatzResearch.WordTrace tailWord_2566988 prefixEnd_2566988 439366226107902627114881 := by
  unfold tailWord_2566988
  simp only [CollatzResearch.WordTrace]
  refine ⟨46812872012124178746086809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62417162682832238328115745 46812872012124178746086809)
  ·
    refine ⟨35109654009093134059565107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46812872012124178746086809 35109654009093134059565107)
    ·
      refine ⟨52664481013639701089347661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35109654009093134059565107 52664481013639701089347661)
      ·
        refine ⟨19749180380114887908505373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52664481013639701089347661 19749180380114887908505373)
        ·
          refine ⟨7405942642543082965689515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19749180380114887908505373 7405942642543082965689515)
          ·
            refine ⟨11108913963814624448534273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7405942642543082965689515 11108913963814624448534273)
            ·
              refine ⟨8331685472860968336400705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11108913963814624448534273 8331685472860968336400705)
              ·
                refine ⟨6248764104645726252300529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8331685472860968336400705 6248764104645726252300529)
                ·
                  refine ⟨4686573078484294689225397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6248764104645726252300529 4686573078484294689225397)
                  ·
                    refine ⟨439366226107902627114881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4686573078484294689225397 439366226107902627114881)
                    ·
                      rfl

theorem cell23_2566988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 2, 5].length) (baseStart_2566988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2566988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2566988 prefixEnd_2566988 := by exact prefixLift 2566988
  have htrace : WordTrace (prefixWord ++ tailWord_2566988) baseStart_2566988 baseEnd_2566988 := by
    simpa [prefixWord, tailWord_2566988, baseEnd_2566988] using wordTrace_append hprefix tailTrace_2566988
  have hstable : (prefixWord ++ tailWord_2566988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2566988).length < 2 ^ (prefixWord ++ tailWord_2566988).sum := by decide
  have hdescent : baseEnd_2566988 < baseStart_2566988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2566988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567022 : List Nat := [4, 1, 2, 3, 2, 2, 1, 1, 2, 5]
def baseStart_2567022 : Nat := 118140960795 + 2567022 * 2 ^ 59
def prefixEnd_2567022 : Nat := 4983230072969 + 3 ^ 40 * 2567022 * 2
def baseEnd_2567022 : Nat := 439372045555320249439829

theorem tailTrace_2567022 : CollatzResearch.WordTrace tailWord_2567022 prefixEnd_2567022 439372045555320249439829 := by
  unfold tailWord_2567022
  simp only [CollatzResearch.WordTrace]
  refine ⟨11703373013265647662363915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62417989404083454199274213 11703373013265647662363915)
  ·
    refine ⟨17555059519898471493545873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11703373013265647662363915 17555059519898471493545873)
    ·
      refine ⟨13166294639923853620159405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17555059519898471493545873 13166294639923853620159405)
      ·
        refine ⟨4937360489971445107559777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13166294639923853620159405 4937360489971445107559777)
        ·
          refine ⟨3703020367478583830669833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4937360489971445107559777 3703020367478583830669833)
          ·
            refine ⟨2777265275608937873002375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3703020367478583830669833 2777265275608937873002375)
            ·
              refine ⟨4165897913413406809503563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2777265275608937873002375 4165897913413406809503563)
              ·
                refine ⟨6248846870120110214255345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4165897913413406809503563 6248846870120110214255345)
                ·
                  refine ⟨4686635152590082660691509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6248846870120110214255345 4686635152590082660691509)
                  ·
                    refine ⟨439372045555320249439829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4686635152590082660691509 439372045555320249439829)
                    ·
                      rfl

theorem cell23_2567022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_2567022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567022 prefixEnd_2567022 := by exact prefixLift 2567022
  have htrace : WordTrace (prefixWord ++ tailWord_2567022) baseStart_2567022 baseEnd_2567022 := by
    simpa [prefixWord, tailWord_2567022, baseEnd_2567022] using wordTrace_append hprefix tailTrace_2567022
  have hstable : (prefixWord ++ tailWord_2567022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567022).length < 2 ^ (prefixWord ++ tailWord_2567022).sum := by decide
  have hdescent : baseEnd_2567022 < baseStart_2567022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567025 : List Nat := [1, 2, 2, 2, 1, 6, 1, 1, 2, 1, 4]
def baseStart_2567025 : Nat := 118140960795 + 2567025 * 2 ^ 59
def prefixEnd_2567025 : Nat := 4983230072969 + 3 ^ 40 * 2567025 * 2
def baseEnd_2567025 : Nat := 1318117677107924236581973

theorem tailTrace_2567025 : CollatzResearch.WordTrace tailWord_2567025 prefixEnd_2567025 1318117677107924236581973 := by
  unfold tailWord_2567025
  simp only [CollatzResearch.WordTrace]
  refine ⟨93627093525114312811270529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62418062350076208540847019 93627093525114312811270529)
  ·
    refine ⟨70220320143835734608452897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93627093525114312811270529 70220320143835734608452897)
    ·
      refine ⟨52665240107876800956339673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70220320143835734608452897 52665240107876800956339673)
      ·
        refine ⟨39498930080907600717254755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52665240107876800956339673 39498930080907600717254755)
        ·
          refine ⟨59248395121361401075882133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39498930080907600717254755 59248395121361401075882133)
          ·
            refine ⟨2777268521313815675431975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 59248395121361401075882133 2777268521313815675431975)
            ·
              refine ⟨4165902781970723513147963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2777268521313815675431975 4165902781970723513147963)
              ·
                refine ⟨6248854172956085269721945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4165902781970723513147963 6248854172956085269721945)
                ·
                  refine ⟨4686640629717063952291459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6248854172956085269721945 4686640629717063952291459)
                  ·
                    refine ⟨7029960944575595928437189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4686640629717063952291459 7029960944575595928437189)
                    ·
                      refine ⟨1318117677107924236581973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7029960944575595928437189 1318117677107924236581973)
                      ·
                        rfl

theorem cell23_2567025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_2567025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567025 prefixEnd_2567025 := by exact prefixLift 2567025
  have htrace : WordTrace (prefixWord ++ tailWord_2567025) baseStart_2567025 baseEnd_2567025 := by
    simpa [prefixWord, tailWord_2567025, baseEnd_2567025] using wordTrace_append hprefix tailTrace_2567025
  have hstable : (prefixWord ++ tailWord_2567025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567025).length < 2 ^ (prefixWord ++ tailWord_2567025).sum := by decide
  have hdescent : baseEnd_2567025 < baseStart_2567025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567035 : List Nat := [1, 1, 1, 1, 1, 5, 3, 5, 1, 4]
def baseStart_2567035 : Nat := 118140960795 + 2567035 * 2 ^ 59
def prefixEnd_2567035 : Nat := 4983230072969 + 3 ^ 40 * 2567035 * 2
def baseEnd_2567035 : Nat := 439374270638156399152309

theorem tailTrace_2567035 : CollatzResearch.WordTrace tailWord_2567035 prefixEnd_2567035 439374270638156399152309 := by
  unfold tailWord_2567035
  simp only [CollatzResearch.WordTrace]
  refine ⟨93627458255078084519134559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62418305503385389679423039 93627458255078084519134559)
  ·
    refine ⟨140441187382617126778701839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93627458255078084519134559 140441187382617126778701839)
    ·
      refine ⟨210661781073925690168052759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140441187382617126778701839 210661781073925690168052759)
      ·
        refine ⟨315992671610888535252079139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210661781073925690168052759 315992671610888535252079139)
        ·
          refine ⟨473989007416332802878118709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315992671610888535252079139 473989007416332802878118709)
          ·
            refine ⟨44436469445281200269823629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 473989007416332802878118709 44436469445281200269823629)
            ·
              refine ⟨16663676041980450101183861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44436469445281200269823629 16663676041980450101183861)
              ·
                refine ⟨1562219628935667196985987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16663676041980450101183861 1562219628935667196985987)
                ·
                  refine ⟨2343329443403500795478981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1562219628935667196985987 2343329443403500795478981)
                  ·
                    refine ⟨439374270638156399152309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2343329443403500795478981 439374270638156399152309)
                    ·
                      rfl

theorem cell23_2567035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 5, 1, 4].length) (baseStart_2567035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567035 prefixEnd_2567035 := by exact prefixLift 2567035
  have htrace : WordTrace (prefixWord ++ tailWord_2567035) baseStart_2567035 baseEnd_2567035 := by
    simpa [prefixWord, tailWord_2567035, baseEnd_2567035] using wordTrace_append hprefix tailTrace_2567035
  have hstable : (prefixWord ++ tailWord_2567035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567035).length < 2 ^ (prefixWord ++ tailWord_2567035).sum := by decide
  have hdescent : baseEnd_2567035 < baseStart_2567035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567048 : List Nat := [2, 1, 3, 3, 2, 2, 1, 1, 8]
def baseStart_2567048 : Nat := 118140960795 + 2567048 * 2 ^ 59
def prefixEnd_2567048 : Nat := 4983230072969 + 3 ^ 40 * 2567048 * 2
def baseEnd_2567048 : Nat := 146458831906997516288263

theorem tailTrace_2567048 : CollatzResearch.WordTrace tailWord_2567048 prefixEnd_2567048 146458831906997516288263 := by
  unfold tailWord_2567048
  simp only [CollatzResearch.WordTrace]
  refine ⟨46813966202015493869678899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62418621602687325159571865 46813966202015493869678899)
  ·
    refine ⟨70220949303023240804518349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46813966202015493869678899 70220949303023240804518349)
    ·
      refine ⟨26332855988633715301694381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70220949303023240804518349 26332855988633715301694381)
      ·
        refine ⟨9874820995737643238135393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26332855988633715301694381 9874820995737643238135393)
        ·
          refine ⟨7406115746803232428601545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9874820995737643238135393 7406115746803232428601545)
          ·
            refine ⟨5554586810102424321451159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7406115746803232428601545 5554586810102424321451159)
            ·
              refine ⟨8331880215153636482176739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5554586810102424321451159 8331880215153636482176739)
              ·
                refine ⟨12497820322730454723265109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8331880215153636482176739 12497820322730454723265109)
                ·
                  refine ⟨146458831906997516288263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12497820322730454723265109 146458831906997516288263)
                  ·
                    rfl

theorem cell23_2567048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 8].length) (baseStart_2567048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567048 prefixEnd_2567048 := by exact prefixLift 2567048
  have htrace : WordTrace (prefixWord ++ tailWord_2567048) baseStart_2567048 baseEnd_2567048 := by
    simpa [prefixWord, tailWord_2567048, baseEnd_2567048] using wordTrace_append hprefix tailTrace_2567048
  have hstable : (prefixWord ++ tailWord_2567048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567048).length < 2 ^ (prefixWord ++ tailWord_2567048).sum := by decide
  have hdescent : baseEnd_2567048 < baseStart_2567048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567051 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 6]
def baseStart_2567051 : Nat := 118140960795 + 2567051 * 2 ^ 59
def prefixEnd_2567051 : Nat := 4983230072969 + 3 ^ 40 * 2567051 * 2
def baseEnd_2567051 : Nat := 1318131027604941134856853

theorem tailTrace_2567051 : CollatzResearch.WordTrace tailWord_2567051 prefixEnd_2567051 1318131027604941134856853 := by
  unfold tailWord_2567051
  simp only [CollatzResearch.WordTrace]
  refine ⟨93628041823020119251717007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62418694548680079501144671 93628041823020119251717007)
  ·
    refine ⟨140442062734530178877575511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93628041823020119251717007 140442062734530178877575511)
    ·
      refine ⟨210663094101795268316363267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140442062734530178877575511 210663094101795268316363267)
      ·
        refine ⟨315994641152692902474544901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210663094101795268316363267 315994641152692902474544901)
        ·
          refine ⟨59248995216129919213977169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 315994641152692902474544901 59248995216129919213977169)
          ·
            refine ⟨44436746412097439410482877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59248995216129919213977169 44436746412097439410482877)
            ·
              refine ⟨16663779904536539778931079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44436746412097439410482877 16663779904536539778931079)
              ·
                refine ⟨24995669856804809668396619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16663779904536539778931079 24995669856804809668396619)
                ·
                  refine ⟨37493504785207214502594929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24995669856804809668396619 37493504785207214502594929)
                  ·
                    refine ⟨28120128588905410876946197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37493504785207214502594929 28120128588905410876946197)
                    ·
                      refine ⟨1318131027604941134856853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28120128588905410876946197 1318131027604941134856853)
                      ·
                        rfl

theorem cell23_2567051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 6].length) (baseStart_2567051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567051 prefixEnd_2567051 := by exact prefixLift 2567051
  have htrace : WordTrace (prefixWord ++ tailWord_2567051) baseStart_2567051 baseEnd_2567051 := by
    simpa [prefixWord, tailWord_2567051, baseEnd_2567051] using wordTrace_append hprefix tailTrace_2567051
  have hstable : (prefixWord ++ tailWord_2567051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567051).length < 2 ^ (prefixWord ++ tailWord_2567051).sum := by decide
  have hdescent : baseEnd_2567051 < baseStart_2567051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567075 : List Nat := [1, 1, 1, 4, 1, 2, 4, 2, 3, 1, 3]
def baseStart_2567075 : Nat := 118140960795 + 2567075 * 2 ^ 59
def prefixEnd_2567075 : Nat := 4983230072969 + 3 ^ 40 * 2567075 * 2
def baseEnd_2567075 : Nat := 1318143351140649040956743

theorem tailTrace_2567075 : CollatzResearch.WordTrace tailWord_2567075 prefixEnd_2567075 1318143351140649040956743 := by
  unfold tailWord_2567075
  simp only [CollatzResearch.WordTrace]
  refine ⟨93628917174933171350590679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62419278116622114233727119 93628917174933171350590679)
  ·
    refine ⟨140443375762399757025886019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93628917174933171350590679 140443375762399757025886019)
    ·
      refine ⟨210665063643599635538829029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140443375762399757025886019 210665063643599635538829029)
      ·
        refine ⟨39499699433174931663530443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 210665063643599635538829029 39499699433174931663530443)
        ·
          refine ⟨59249549149762397495295665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39499699433174931663530443 59249549149762397495295665)
          ·
            refine ⟨44437161862321798121471749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59249549149762397495295665 44437161862321798121471749)
            ·
              refine ⟨8331967849185337147775953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44437161862321798121471749 8331967849185337147775953)
              ·
                refine ⟨6248975886889002860831965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8331967849185337147775953 6248975886889002860831965)
                ·
                  refine ⟨2343365957583376072811987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6248975886889002860831965 2343365957583376072811987)
                  ·
                    refine ⟨3515048936375064109217981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2343365957583376072811987 3515048936375064109217981)
                    ·
                      refine ⟨1318143351140649040956743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3515048936375064109217981 1318143351140649040956743)
                      ·
                        rfl

theorem cell23_2567075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 3, 1, 3].length) (baseStart_2567075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567075 prefixEnd_2567075 := by exact prefixLift 2567075
  have htrace : WordTrace (prefixWord ++ tailWord_2567075) baseStart_2567075 baseEnd_2567075 := by
    simpa [prefixWord, tailWord_2567075, baseEnd_2567075] using wordTrace_append hprefix tailTrace_2567075
  have hstable : (prefixWord ++ tailWord_2567075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567075).length < 2 ^ (prefixWord ++ tailWord_2567075).sum := by decide
  have hdescent : baseEnd_2567075 < baseStart_2567075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567102 : List Nat := [4, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2]
def baseStart_2567102 : Nat := 118140960795 + 2567102 * 2 ^ 59
def prefixEnd_2567102 : Nat := 4983230072969 + 3 ^ 40 * 2567102 * 2
def baseEnd_2567102 : Nat := 1318157215118320435319119

theorem tailTrace_2567102 : CollatzResearch.WordTrace tailWord_2567102 prefixEnd_2567102 1318157215118320435319119 := by
  unfold tailWord_2567102
  simp only [CollatzResearch.WordTrace]
  refine ⟨11703737743229419370227945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62419934630556903307882373 11703737743229419370227945)
  ·
    refine ⟨8777803307422064527670959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11703737743229419370227945 8777803307422064527670959)
    ·
      refine ⟨13166704961133096791506439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8777803307422064527670959 13166704961133096791506439)
      ·
        refine ⟨19750057441699645187259659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13166704961133096791506439 19750057441699645187259659)
        ·
          refine ⟨29625086162549467780889489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19750057441699645187259659 29625086162549467780889489)
          ·
            refine ⟨22218814621912100835667117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29625086162549467780889489 22218814621912100835667117)
            ·
              refine ⟨8332055483217037813375169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22218814621912100835667117 8332055483217037813375169)
              ·
                refine ⟨6249041612412778360031377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8332055483217037813375169 6249041612412778360031377)
                ·
                  refine ⟨4686781209309583770023533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6249041612412778360031377 4686781209309583770023533)
                  ·
                    refine ⟨1757542953491093913758825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4686781209309583770023533 1757542953491093913758825)
                    ·
                      refine ⟨1318157215118320435319119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1757542953491093913758825 1318157215118320435319119)
                      ·
                        rfl

theorem cell23_2567102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_2567102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567102 prefixEnd_2567102 := by exact prefixLift 2567102
  have htrace : WordTrace (prefixWord ++ tailWord_2567102) baseStart_2567102 baseEnd_2567102 := by
    simpa [prefixWord, tailWord_2567102, baseEnd_2567102] using wordTrace_append hprefix tailTrace_2567102
  have hstable : (prefixWord ++ tailWord_2567102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567102).length < 2 ^ (prefixWord ++ tailWord_2567102).sum := by decide
  have hdescent : baseEnd_2567102 < baseStart_2567102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567128 : List Nat := [2, 1, 2, 2, 2, 3, 2, 1, 1, 1, 6]
def baseStart_2567128 : Nat := 118140960795 + 2567128 * 2 ^ 59
def prefixEnd_2567128 : Nat := 4983230072969 + 3 ^ 40 * 2567128 * 2
def baseEnd_2567128 : Nat := 1318170565615337333593999

theorem tailTrace_2567128 : CollatzResearch.WordTrace tailWord_2567128 prefixEnd_2567128 1318170565615337333593999 := by
  unfold tailWord_2567128
  simp only [CollatzResearch.WordTrace]
  refine ⟨46815425121870580701135019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62420566829160774268180025 46815425121870580701135019)
  ·
    refine ⟨70223137682805871051702529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46815425121870580701135019 70223137682805871051702529)
    ·
      refine ⟨52667353262104403288776897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70223137682805871051702529 52667353262104403288776897)
      ·
        refine ⟨39500514946578302466582673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52667353262104403288776897 39500514946578302466582673)
        ·
          refine ⟨29625386209933726849937005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39500514946578302466582673 29625386209933726849937005)
          ·
            refine ⟨11109519828725147568726377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29625386209933726849937005 11109519828725147568726377)
            ·
              refine ⟨8332139871543860676544783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11109519828725147568726377 8332139871543860676544783)
              ·
                refine ⟨12498209807315791014817175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8332139871543860676544783 12498209807315791014817175)
                ·
                  refine ⟨18747314710973686522225763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12498209807315791014817175 18747314710973686522225763)
                  ·
                    refine ⟨28120972066460529783338645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18747314710973686522225763 28120972066460529783338645)
                    ·
                      refine ⟨1318170565615337333593999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28120972066460529783338645 1318170565615337333593999)
                      ·
                        rfl

theorem cell23_2567128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_2567128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567128 prefixEnd_2567128 := by exact prefixLift 2567128
  have htrace : WordTrace (prefixWord ++ tailWord_2567128) baseStart_2567128 baseEnd_2567128 := by
    simpa [prefixWord, tailWord_2567128, baseEnd_2567128] using wordTrace_append hprefix tailTrace_2567128
  have hstable : (prefixWord ++ tailWord_2567128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567128).length < 2 ^ (prefixWord ++ tailWord_2567128).sum := by decide
  have hdescent : baseEnd_2567128 < baseStart_2567128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567182 : List Nat := [4, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3]
def baseStart_2567182 : Nat := 118140960795 + 2567182 * 2 ^ 59
def prefixEnd_2567182 : Nat := 4983230072969 + 3 ^ 40 * 2567182 * 2
def baseEnd_2567182 : Nat := 1318198293570680122318751

theorem tailTrace_2567182 : CollatzResearch.WordTrace tailWord_2567182 prefixEnd_2567182 1318198293570680122318751 := by
  unfold tailWord_2567182
  simp only [CollatzResearch.WordTrace]
  refine ⟨11704102473193191078091975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62421879857030352416490533 11704102473193191078091975)
  ·
    refine ⟨17556153709789786617137963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11704102473193191078091975 17556153709789786617137963)
    ·
      refine ⟨26334230564684679925706945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17556153709789786617137963 26334230564684679925706945)
      ·
        refine ⟨19750672923513509944280209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26334230564684679925706945 19750672923513509944280209)
        ·
          refine ⟨14813004692635132458210157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19750672923513509944280209 14813004692635132458210157)
          ·
            refine ⟨5554876759738174671828809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14813004692635132458210157 5554876759738174671828809)
            ·
              refine ⟨4166157569803631003871607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5554876759738174671828809 4166157569803631003871607)
              ·
                refine ⟨6249236354705446505807411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4166157569803631003871607 6249236354705446505807411)
                ·
                  refine ⟨9373854532058169758711117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6249236354705446505807411 9373854532058169758711117)
                  ·
                    refine ⟨3515195449521813659516669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9373854532058169758711117 3515195449521813659516669)
                    ·
                      refine ⟨1318198293570680122318751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3515195449521813659516669 1318198293570680122318751)
                      ·
                        rfl

theorem cell23_2567182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_2567182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567182 prefixEnd_2567182 := by exact prefixLift 2567182
  have htrace : WordTrace (prefixWord ++ tailWord_2567182) baseStart_2567182 baseEnd_2567182 := by
    simpa [prefixWord, tailWord_2567182, baseEnd_2567182] using wordTrace_append hprefix tailTrace_2567182
  have hstable : (prefixWord ++ tailWord_2567182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567182).length < 2 ^ (prefixWord ++ tailWord_2567182).sum := by decide
  have hdescent : baseEnd_2567182 < baseStart_2567182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567192 : List Nat := [2, 1, 2, 3, 2, 2, 2, 1, 3, 3, 2]
def baseStart_2567192 : Nat := 118140960795 + 2567192 * 2 ^ 59
def prefixEnd_2567192 : Nat := 4983230072969 + 3 ^ 40 * 2567192 * 2
def baseEnd_2567192 : Nat := 1318203428377225083193705

theorem tailTrace_2567192 : CollatzResearch.WordTrace tailWord_2567192 prefixEnd_2567192 1318203428377225083193705 := by
  unfold tailWord_2567192
  simp only [CollatzResearch.WordTrace]
  refine ⟨46816592257754650166299915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62422123010339533555066553 46816592257754650166299915)
  ·
    refine ⟨70224888386631975249449873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46816592257754650166299915 70224888386631975249449873)
    ·
      refine ⟨52668666289973981437087405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70224888386631975249449873 52668666289973981437087405)
      ·
        refine ⟨19750749858740243038907777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52668666289973981437087405 19750749858740243038907777)
        ·
          refine ⟨14813062394055182279180833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19750749858740243038907777 14813062394055182279180833)
          ·
            refine ⟨11109796795541386709385625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14813062394055182279180833 11109796795541386709385625)
            ·
              refine ⟨8332347596656040032039219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11109796795541386709385625 8332347596656040032039219)
              ·
                refine ⟨12498521394984060048058829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8332347596656040032039219 12498521394984060048058829)
                ·
                  refine ⟨4686945523119022518022061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12498521394984060048058829 4686945523119022518022061)
                  ·
                    refine ⟨1757604571169633444258273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4686945523119022518022061 1757604571169633444258273)
                    ·
                      refine ⟨1318203428377225083193705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1757604571169633444258273 1318203428377225083193705)
                      ·
                        rfl

theorem cell23_2567192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_2567192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567192 prefixEnd_2567192 := by exact prefixLift 2567192
  have htrace : WordTrace (prefixWord ++ tailWord_2567192) baseStart_2567192 baseEnd_2567192 := by
    simpa [prefixWord, tailWord_2567192, baseEnd_2567192] using wordTrace_append hprefix tailTrace_2567192
  have hstable : (prefixWord ++ tailWord_2567192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567192).length < 2 ^ (prefixWord ++ tailWord_2567192).sum := by decide
  have hdescent : baseEnd_2567192 < baseStart_2567192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567239 : List Nat := [1, 1, 4, 1, 3, 4, 1, 1, 1, 4, 2]
def baseStart_2567239 : Nat := 118140960795 + 2567239 * 2 ^ 59
def prefixEnd_2567239 : Nat := 4983230072969 + 3 ^ 40 * 2567239 * 2
def baseEnd_2567239 : Nat := 1318227561967986399305989

theorem tailTrace_2567239 : CollatzResearch.WordTrace tailWord_2567239 prefixEnd_2567239 1318227561967986399305989 := by
  unfold tailWord_2567239
  simp only [CollatzResearch.WordTrace]
  refine ⟨93634898746339027359560771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62423265830892684906373847 93634898746339027359560771)
  ·
    refine ⟨140452348119508541039341157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93634898746339027359560771 140452348119508541039341157)
    ·
      refine ⟨26334815272407851444876467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140452348119508541039341157 26334815272407851444876467)
      ·
        refine ⟨39502222908611777167314701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26334815272407851444876467 39502222908611777167314701)
        ·
          refine ⟨14813333590729416437743013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39502222908611777167314701 14813333590729416437743013)
          ·
            refine ⟨2777500048261765582076815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14813333590729416437743013 2777500048261765582076815)
            ·
              refine ⟨4166250072392648373115223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2777500048261765582076815 4166250072392648373115223)
              ·
                refine ⟨6249375108588972559672835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4166250072392648373115223 6249375108588972559672835)
                ·
                  refine ⟨9374062662883458839509253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6249375108588972559672835 9374062662883458839509253)
                  ·
                    refine ⟨1757636749290648532407985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9374062662883458839509253 1757636749290648532407985)
                    ·
                      refine ⟨1318227561967986399305989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1757636749290648532407985 1318227561967986399305989)
                      ·
                        rfl

theorem cell23_2567239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 4, 2].length) (baseStart_2567239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567239 prefixEnd_2567239 := by exact prefixLift 2567239
  have htrace : WordTrace (prefixWord ++ tailWord_2567239) baseStart_2567239 baseEnd_2567239 := by
    simpa [prefixWord, tailWord_2567239, baseEnd_2567239] using wordTrace_append hprefix tailTrace_2567239
  have hstable : (prefixWord ++ tailWord_2567239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567239).length < 2 ^ (prefixWord ++ tailWord_2567239).sum := by decide
  have hdescent : baseEnd_2567239 < baseStart_2567239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567282 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 2, 5, 2]
def baseStart_2567282 : Nat := 118140960795 + 2567282 * 2 ^ 59
def prefixEnd_2567282 : Nat := 4983230072969 + 3 ^ 40 * 2567282 * 2
def baseEnd_2567282 : Nat := 1318249641636129731068291

theorem tailTrace_2567282 : CollatzResearch.WordTrace tailWord_2567282 prefixEnd_2567282 1318249641636129731068291 := by
  unfold tailWord_2567282
  simp only [CollatzResearch.WordTrace]
  refine ⟨23409116771295811425844025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62424311390122163802250733 23409116771295811425844025)
  ·
    refine ⟨17556837578471858569383019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23409116771295811425844025 17556837578471858569383019)
    ·
      refine ⟨26335256367707787854074529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17556837578471858569383019 26335256367707787854074529)
      ·
        refine ⟨19751442275780840890555897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26335256367707787854074529 19751442275780840890555897)
        ·
          refine ⟨14813581706835630667916923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19751442275780840890555897 14813581706835630667916923)
          ·
            refine ⟨22220372560253446001875385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14813581706835630667916923 22220372560253446001875385)
            ·
              refine ⟨16665279420190084501406539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22220372560253446001875385 16665279420190084501406539)
              ·
                refine ⟨24997919130285126752109809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16665279420190084501406539 24997919130285126752109809)
                ·
                  refine ⟨18748439347713845064082357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24997919130285126752109809 18748439347713845064082357)
                  ·
                    refine ⟨1757666188848172974757721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18748439347713845064082357 1757666188848172974757721)
                    ·
                      refine ⟨1318249641636129731068291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1757666188848172974757721 1318249641636129731068291)
                      ·
                        rfl

theorem cell23_2567282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_2567282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567282 prefixEnd_2567282 := by exact prefixLift 2567282
  have htrace : WordTrace (prefixWord ++ tailWord_2567282) baseStart_2567282 baseEnd_2567282 := by
    simpa [prefixWord, tailWord_2567282, baseEnd_2567282] using wordTrace_append hprefix tailTrace_2567282
  have hstable : (prefixWord ++ tailWord_2567282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567282).length < 2 ^ (prefixWord ++ tailWord_2567282).sum := by decide
  have hdescent : baseEnd_2567282 < baseStart_2567282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567315 : List Nat := [1, 1, 1, 2, 1, 2, 4, 3, 1, 4, 3]
def baseStart_2567315 : Nat := 118140960795 + 2567315 * 2 ^ 59
def prefixEnd_2567315 : Nat := 4983230072969 + 3 ^ 40 * 2567315 * 2
def baseEnd_2567315 : Nat := 1318266586497728101955639

theorem tailTrace_2567315 : CollatzResearch.WordTrace tailWord_2567315 prefixEnd_2567315 1318266586497728101955639 := by
  unfold tailWord_2567315
  simp only [CollatzResearch.WordTrace]
  refine ⟨93637670694063692339327399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62425113796042461559551599 93637670694063692339327399)
  ·
    refine ⟨140456506041095538508991099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93637670694063692339327399 140456506041095538508991099)
    ·
      refine ⟨210684759061643307763486649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140456506041095538508991099 210684759061643307763486649)
      ·
        refine ⟨158013569296232480822614987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210684759061643307763486649 158013569296232480822614987)
        ·
          refine ⟨237020353944348721233922481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158013569296232480822614987 237020353944348721233922481)
          ·
            refine ⟨177765265458261540925441861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237020353944348721233922481 177765265458261540925441861)
            ·
              refine ⟨33330987273424038923520349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 177765265458261540925441861 33330987273424038923520349)
              ·
                refine ⟨12499120227534014596320131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33330987273424038923520349 12499120227534014596320131)
                ·
                  refine ⟨18748680341301021894480197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12499120227534014596320131 18748680341301021894480197)
                  ·
                    refine ⟨3515377563993941605215037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18748680341301021894480197 3515377563993941605215037)
                    ·
                      refine ⟨1318266586497728101955639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3515377563993941605215037 1318266586497728101955639)
                      ·
                        rfl

theorem cell23_2567315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 4, 3].length) (baseStart_2567315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567315 prefixEnd_2567315 := by exact prefixLift 2567315
  have htrace : WordTrace (prefixWord ++ tailWord_2567315) baseStart_2567315 baseEnd_2567315 := by
    simpa [prefixWord, tailWord_2567315, baseEnd_2567315] using wordTrace_append hprefix tailTrace_2567315
  have hstable : (prefixWord ++ tailWord_2567315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567315).length < 2 ^ (prefixWord ++ tailWord_2567315).sum := by decide
  have hdescent : baseEnd_2567315 < baseStart_2567315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567325 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 2, 1, 6]
def baseStart_2567325 : Nat := 118140960795 + 2567325 * 2 ^ 59
def prefixEnd_2567325 : Nat := 4983230072969 + 3 ^ 40 * 2567325 * 2
def baseEnd_2567325 : Nat := 1318271721304273062830593

theorem tailTrace_2567325 : CollatzResearch.WordTrace tailWord_2567325 prefixEnd_2567325 1318271721304273062830593 := by
  unfold tailWord_2567325
  simp only [CollatzResearch.WordTrace]
  refine ⟨93638035424027464047191429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62425356949351642698127619 93638035424027464047191429)
  ·
    refine ⟨17557131642005149508848393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93638035424027464047191429 17557131642005149508848393)
    ·
      refine ⟨13167848731503862131636295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17557131642005149508848393 13167848731503862131636295)
      ·
        refine ⟨19751773097255793197454443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13167848731503862131636295 19751773097255793197454443)
        ·
          refine ⟨29627659645883689796181665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19751773097255793197454443 29627659645883689796181665)
          ·
            refine ⟨22220744734412767347136249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29627659645883689796181665 22220744734412767347136249)
            ·
              refine ⟨16665558550809575510352187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22220744734412767347136249 16665558550809575510352187)
              ·
                refine ⟨24998337826214363265528281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16665558550809575510352187 24998337826214363265528281)
                ·
                  refine ⟨18748753369660772449146211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24998337826214363265528281 18748753369660772449146211)
                  ·
                    refine ⟨28123130054491158673719317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18748753369660772449146211 28123130054491158673719317)
                    ·
                      refine ⟨1318271721304273062830593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28123130054491158673719317 1318271721304273062830593)
                      ·
                        rfl

theorem cell23_2567325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_2567325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567325 prefixEnd_2567325 := by exact prefixLift 2567325
  have htrace : WordTrace (prefixWord ++ tailWord_2567325) baseStart_2567325 baseEnd_2567325 := by
    simpa [prefixWord, tailWord_2567325, baseEnd_2567325] using wordTrace_append hprefix tailTrace_2567325
  have hstable : (prefixWord ++ tailWord_2567325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567325).length < 2 ^ (prefixWord ++ tailWord_2567325).sum := by decide
  have hdescent : baseEnd_2567325 < baseStart_2567325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567396 : List Nat := [2, 3, 1, 1, 1, 2, 4, 4, 1, 1, 3]
def baseStart_2567396 : Nat := 118140960795 + 2567396 * 2 ^ 59
def prefixEnd_2567396 : Nat := 4983230072969 + 3 ^ 40 * 2567396 * 2
def baseEnd_2567396 : Nat := 1318308178430742285042767

theorem tailTrace_2567396 : CollatzResearch.WordTrace tailWord_2567396 prefixEnd_2567396 1318308178430742285042767 := by
  unfold tailWord_2567396
  simp only [CollatzResearch.WordTrace]
  refine ⟨46820312503385121586513021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62427083337846828782017361 46820312503385121586513021)
  ·
    refine ⟨17557617188769420594942383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46820312503385121586513021 17557617188769420594942383)
    ·
      refine ⟨26336425783154130892413575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17557617188769420594942383 26336425783154130892413575)
      ·
        refine ⟨39504638674731196338620363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26336425783154130892413575 39504638674731196338620363)
        ·
          refine ⟨59256958012096794507930545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39504638674731196338620363 59256958012096794507930545)
          ·
            refine ⟨44442718509072595880947909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59256958012096794507930545 44442718509072595880947909)
            ·
              refine ⟨8333009720451111727677733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44442718509072595880947909 8333009720451111727677733)
              ·
                refine ⟨1562439322584583448939575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8333009720451111727677733 1562439322584583448939575)
                ·
                  refine ⟨2343658983876875173409363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1562439322584583448939575 2343658983876875173409363)
                  ·
                    refine ⟨3515488475815312760114045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2343658983876875173409363 3515488475815312760114045)
                    ·
                      refine ⟨1318308178430742285042767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3515488475815312760114045 1318308178430742285042767)
                      ·
                        rfl

theorem cell23_2567396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 4, 1, 1, 3].length) (baseStart_2567396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567396 prefixEnd_2567396 := by exact prefixLift 2567396
  have htrace : WordTrace (prefixWord ++ tailWord_2567396) baseStart_2567396 baseEnd_2567396 := by
    simpa [prefixWord, tailWord_2567396, baseEnd_2567396] using wordTrace_append hprefix tailTrace_2567396
  have hstable : (prefixWord ++ tailWord_2567396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567396).length < 2 ^ (prefixWord ++ tailWord_2567396).sum := by decide
  have hdescent : baseEnd_2567396 < baseStart_2567396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567415 : List Nat := [1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 6]
def baseStart_2567415 : Nat := 118140960795 + 2567415 * 2 ^ 59
def prefixEnd_2567415 : Nat := 4983230072969 + 3 ^ 40 * 2567415 * 2
def baseEnd_2567415 : Nat := 1318317934563177710705179

theorem tailTrace_2567415 : CollatzResearch.WordTrace tailWord_2567415 prefixEnd_2567415 1318317934563177710705179 := by
  unfold tailWord_2567415
  simp only [CollatzResearch.WordTrace]
  refine ⟨93641317993701409417967699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62427545329134272945311799 93641317993701409417967699)
  ·
    refine ⟨140461976990552114126951549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93641317993701409417967699 140461976990552114126951549)
    ·
      refine ⟨52673241371457042797606831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140461976990552114126951549 52673241371457042797606831)
      ·
        refine ⟨79009862057185564196410247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52673241371457042797606831 79009862057185564196410247)
        ·
          refine ⟨118514793085778346294615371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79009862057185564196410247 118514793085778346294615371)
          ·
            refine ⟨177772189628667519441923057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118514793085778346294615371 177772189628667519441923057)
            ·
              refine ⟨133329142221500639581442293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177772189628667519441923057 133329142221500639581442293)
              ·
                refine ⟨12499607083265684960760215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133329142221500639581442293 12499607083265684960760215)
                ·
                  refine ⟨18749410624898527441140323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12499607083265684960760215 18749410624898527441140323)
                  ·
                    refine ⟨28124115937347791161710485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18749410624898527441140323 28124115937347791161710485)
                    ·
                      refine ⟨1318317934563177710705179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28124115937347791161710485 1318317934563177710705179)
                      ·
                        rfl

theorem cell23_2567415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_2567415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567415 prefixEnd_2567415 := by exact prefixLift 2567415
  have htrace : WordTrace (prefixWord ++ tailWord_2567415) baseStart_2567415 baseEnd_2567415 := by
    simpa [prefixWord, tailWord_2567415, baseEnd_2567415] using wordTrace_append hprefix tailTrace_2567415
  have hstable : (prefixWord ++ tailWord_2567415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567415).length < 2 ^ (prefixWord ++ tailWord_2567415).sum := by decide
  have hdescent : baseEnd_2567415 < baseStart_2567415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567453 : List Nat := [1, 4, 2, 3, 1, 1, 3, 1, 3, 2, 2]
def baseStart_2567453 : Nat := 118140960795 + 2567453 * 2 ^ 59
def prefixEnd_2567453 : Nat := 4983230072969 + 3 ^ 40 * 2567453 * 2
def baseEnd_2567453 : Nat := 1318337446828048562030005

theorem tailTrace_2567453 : CollatzResearch.WordTrace tailWord_2567453 prefixEnd_2567453 1318337446828048562030005 := by
  unfold tailWord_2567453
  simp only [CollatzResearch.WordTrace]
  refine ⟨93642703967563741907851013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62428469311709161271900675 93642703967563741907851013)
  ·
    refine ⟨17558006993918201607722065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93642703967563741907851013 17558006993918201607722065)
    ·
      refine ⟨13168505245438651205791549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17558006993918201607722065 13168505245438651205791549)
      ·
        refine ⟨4938189467039494202171831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13168505245438651205791549 4938189467039494202171831)
        ·
          refine ⟨7407284200559241303257747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4938189467039494202171831 7407284200559241303257747)
          ·
            refine ⟨11110926300838861954886621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7407284200559241303257747 11110926300838861954886621)
            ·
              refine ⟨4166597362814573233082483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11110926300838861954886621 4166597362814573233082483)
              ·
                refine ⟨6249896044221859849623725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4166597362814573233082483 6249896044221859849623725)
                ·
                  refine ⟨2343711016583197443608897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6249896044221859849623725 2343711016583197443608897)
                  ·
                    refine ⟨1757783262437398082706673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2343711016583197443608897 1757783262437398082706673)
                    ·
                      refine ⟨1318337446828048562030005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1757783262437398082706673 1318337446828048562030005)
                      ·
                        rfl

theorem cell23_2567453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_2567453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567453 prefixEnd_2567453 := by exact prefixLift 2567453
  have htrace : WordTrace (prefixWord ++ tailWord_2567453) baseStart_2567453 baseEnd_2567453 := by
    simpa [prefixWord, tailWord_2567453, baseEnd_2567453] using wordTrace_append hprefix tailTrace_2567453
  have hstable : (prefixWord ++ tailWord_2567453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567453).length < 2 ^ (prefixWord ++ tailWord_2567453).sum := by decide
  have hdescent : baseEnd_2567453 < baseStart_2567453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567502 : List Nat := [4, 1, 1, 1, 1, 1, 4, 2, 2, 6]
def baseStart_2567502 : Nat := 118140960795 + 2567502 * 2 ^ 59
def prefixEnd_2567502 : Nat := 4983230072969 + 3 ^ 40 * 2567502 * 2
def baseEnd_2567502 : Nat := 439454202460039623439093

theorem tailTrace_2567502 : CollatzResearch.WordTrace tailWord_2567502 prefixEnd_2567502 439454202460039623439093 := by
  unfold tailWord_2567502
  simp only [CollatzResearch.WordTrace]
  refine ⟨11705561393048277909548095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62429660762924148850923173 11705561393048277909548095)
  ·
    refine ⟨17558342089572416864322143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11705561393048277909548095 17558342089572416864322143)
    ·
      refine ⟨26337513134358625296483215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17558342089572416864322143 26337513134358625296483215)
      ·
        refine ⟨39506269701537937944724823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26337513134358625296483215 39506269701537937944724823)
        ·
          refine ⟨59259404552306906917087235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39506269701537937944724823 59259404552306906917087235)
          ·
            refine ⟨88889106828460360375630853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59259404552306906917087235 88889106828460360375630853)
            ·
              refine ⟨16666707530336317570430785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88889106828460360375630853 16666707530336317570430785)
              ·
                refine ⟨12500030647752238177823089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16666707530336317570430785 12500030647752238177823089)
                ·
                  refine ⟨9375022985814178633367317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12500030647752238177823089 9375022985814178633367317)
                  ·
                    refine ⟨439454202460039623439093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9375022985814178633367317 439454202460039623439093)
                    ·
                      rfl

theorem cell23_2567502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_2567502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567502 prefixEnd_2567502 := by exact prefixLift 2567502
  have htrace : WordTrace (prefixWord ++ tailWord_2567502) baseStart_2567502 baseEnd_2567502 := by
    simpa [prefixWord, tailWord_2567502, baseEnd_2567502] using wordTrace_append hprefix tailTrace_2567502
  have hstable : (prefixWord ++ tailWord_2567502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567502).length < 2 ^ (prefixWord ++ tailWord_2567502).sum := by decide
  have hdescent : baseEnd_2567502 < baseStart_2567502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567510 : List Nat := [5, 2, 3, 1, 1, 2, 1, 8]
def baseStart_2567510 : Nat := 118140960795 + 2567510 * 2 ^ 59
def prefixEnd_2567510 : Nat := 4983230072969 + 3 ^ 40 * 2567510 * 2
def baseEnd_2567510 : Nat := 48828396860198327371009

theorem tailTrace_2567510 : CollatzResearch.WordTrace tailWord_2567510 prefixEnd_2567510 48828396860198327371009 := by
  unfold tailWord_2567510
  simp only [CollatzResearch.WordTrace]
  refine ⟨5852798933022327540167249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62429855285571493761783989 5852798933022327540167249)
  ·
    refine ⟨4389599199766745655125437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5852798933022327540167249 4389599199766745655125437)
    ·
      refine ⟨1646099699912529620672039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4389599199766745655125437 1646099699912529620672039)
      ·
        refine ⟨2469149549868794431008059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1646099699912529620672039 2469149549868794431008059)
        ·
          refine ⟨3703724324803191646512089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2469149549868794431008059 3703724324803191646512089)
          ·
            refine ⟨2777793243602393734884067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3703724324803191646512089 2777793243602393734884067)
            ·
              refine ⟨4166689865403590602326101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2777793243602393734884067 4166689865403590602326101)
              ·
                refine ⟨48828396860198327371009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4166689865403590602326101 48828396860198327371009)
                ·
                  rfl

theorem cell23_2567510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 8].length) (baseStart_2567510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567510 prefixEnd_2567510 := by exact prefixLift 2567510
  have htrace : WordTrace (prefixWord ++ tailWord_2567510) baseStart_2567510 baseEnd_2567510 := by
    simpa [prefixWord, tailWord_2567510, baseEnd_2567510] using wordTrace_append hprefix tailTrace_2567510
  have hstable : (prefixWord ++ tailWord_2567510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567510).length < 2 ^ (prefixWord ++ tailWord_2567510).sum := by decide
  have hdescent : baseEnd_2567510 < baseStart_2567510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567512 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 1, 6, 3]
def baseStart_2567512 : Nat := 118140960795 + 2567512 * 2 ^ 59
def prefixEnd_2567512 : Nat := 4983230072969 + 3 ^ 40 * 2567512 * 2
def baseEnd_2567512 : Nat := 1318367742186663831192233

theorem tailTrace_2567512 : CollatzResearch.WordTrace tailWord_2567512 prefixEnd_2567512 1318367742186663831192233 := by
  unfold tailWord_2567512
  simp only [CollatzResearch.WordTrace]
  refine ⟨46822427937174997492124395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62429903916233329989499193 46822427937174997492124395)
  ·
    refine ⟨70233641905762496238186593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46822427937174997492124395 70233641905762496238186593)
    ·
      refine ⟨52675231429321872178639945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70233641905762496238186593 52675231429321872178639945)
      ·
        refine ⟨39506423571991404133979959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52675231429321872178639945 39506423571991404133979959)
        ·
          refine ⟨59259635357987106200969939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39506423571991404133979959 59259635357987106200969939)
          ·
            refine ⟨88889453036980659301454909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59259635357987106200969939 88889453036980659301454909)
            ·
              refine ⟨33333544888867747238045591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88889453036980659301454909 33333544888867747238045591)
              ·
                refine ⟨50000317333301620857068387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33333544888867747238045591 50000317333301620857068387)
                ·
                  refine ⟨75000475999952431285602581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50000317333301620857068387 75000475999952431285602581)
                  ·
                    refine ⟨3515647312497770216512621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 75000475999952431285602581 3515647312497770216512621)
                    ·
                      refine ⟨1318367742186663831192233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3515647312497770216512621 1318367742186663831192233)
                      ·
                        rfl

theorem cell23_2567512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_2567512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567512 prefixEnd_2567512 := by exact prefixLift 2567512
  have htrace : WordTrace (prefixWord ++ tailWord_2567512) baseStart_2567512 baseEnd_2567512 := by
    simpa [prefixWord, tailWord_2567512, baseEnd_2567512] using wordTrace_append hprefix tailTrace_2567512
  have hstable : (prefixWord ++ tailWord_2567512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567512).length < 2 ^ (prefixWord ++ tailWord_2567512).sum := by decide
  have hdescent : baseEnd_2567512 < baseStart_2567512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567532 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 9]
def baseStart_2567532 : Nat := 118140960795 + 2567532 * 2 ^ 59
def prefixEnd_2567532 : Nat := 4983230072969 + 3 ^ 40 * 2567532 * 2
def baseEnd_2567532 : Nat := 146486445755528194771349

theorem tailTrace_2567532 : CollatzResearch.WordTrace tailWord_2567532 prefixEnd_2567532 146486445755528194771349 := by
  unfold tailWord_2567532
  simp only [CollatzResearch.WordTrace]
  refine ⟨46822792667138769199988425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62430390222851692266651233 46822792667138769199988425)
  ·
    refine ⟨35117094500354076899991319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46822792667138769199988425 35117094500354076899991319)
    ·
      refine ⟨52675641750531115349986979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35117094500354076899991319 52675641750531115349986979)
      ·
        refine ⟨79013462625796673024980469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52675641750531115349986979 79013462625796673024980469)
        ·
          refine ⟨7407512121168438096091919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79013462625796673024980469 7407512121168438096091919)
          ·
            refine ⟨11111268181752657144137879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7407512121168438096091919 11111268181752657144137879)
            ·
              refine ⟨16666902272628985716206819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11111268181752657144137879 16666902272628985716206819)
              ·
                refine ⟨25000353408943478574310229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16666902272628985716206819 25000353408943478574310229)
                ·
                  refine ⟨146486445755528194771349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25000353408943478574310229 146486445755528194771349)
                  ·
                    rfl

theorem cell23_2567532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 9].length) (baseStart_2567532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567532 prefixEnd_2567532 := by exact prefixLift 2567532
  have htrace : WordTrace (prefixWord ++ tailWord_2567532) baseStart_2567532 baseEnd_2567532 := by
    simpa [prefixWord, tailWord_2567532, baseEnd_2567532] using wordTrace_append hprefix tailTrace_2567532
  have hstable : (prefixWord ++ tailWord_2567532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567532).length < 2 ^ (prefixWord ++ tailWord_2567532).sum := by decide
  have hdescent : baseEnd_2567532 < baseStart_2567532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567559 : List Nat := [1, 1, 4, 2, 2, 2, 1, 2, 2, 3, 3]
def baseStart_2567559 : Nat := 118140960795 + 2567559 * 2 ^ 59
def prefixEnd_2567559 : Nat := 4983230072969 + 3 ^ 40 * 2567559 * 2
def baseEnd_2567559 : Nat := 1318391875777425147304517

theorem tailTrace_2567559 : CollatzResearch.WordTrace tailWord_2567559 prefixEnd_2567559 1318391875777425147304517 := by
  unfold tailWord_2567559
  simp only [CollatzResearch.WordTrace]
  refine ⟨93646570105179722011209731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62431046736786481340806487 93646570105179722011209731)
  ·
    refine ⟨140469855157769583016814597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93646570105179722011209731 140469855157769583016814597)
    ·
      refine ⟨26338097842081796815652737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140469855157769583016814597 26338097842081796815652737)
      ·
        refine ⟨19753573381561347611739553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26338097842081796815652737 19753573381561347611739553)
        ·
          refine ⟨14815180036171010708804665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19753573381561347611739553 14815180036171010708804665)
          ·
            refine ⟨11111385027128258031603499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14815180036171010708804665 11111385027128258031603499)
            ·
              refine ⟨16667077540692387047405249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11111385027128258031603499 16667077540692387047405249)
              ·
                refine ⟨12500308155519290285553937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16667077540692387047405249 12500308155519290285553937)
                ·
                  refine ⟨9375231116639467714165453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12500308155519290285553937 9375231116639467714165453)
                  ·
                    refine ⟨3515711668739800392812045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9375231116639467714165453 3515711668739800392812045)
                    ·
                      refine ⟨1318391875777425147304517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3515711668739800392812045 1318391875777425147304517)
                      ·
                        rfl

theorem cell23_2567559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_2567559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567559 prefixEnd_2567559 := by exact prefixLift 2567559
  have htrace : WordTrace (prefixWord ++ tailWord_2567559) baseStart_2567559 baseEnd_2567559 := by
    simpa [prefixWord, tailWord_2567559, baseEnd_2567559] using wordTrace_append hprefix tailTrace_2567559
  have hstable : (prefixWord ++ tailWord_2567559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567559).length < 2 ^ (prefixWord ++ tailWord_2567559).sum := by decide
  have hdescent : baseEnd_2567559 < baseStart_2567559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567560 : List Nat := [2, 1, 3, 3, 1, 4, 1, 2, 2, 2, 2]
def baseStart_2567560 : Nat := 118140960795 + 2567560 * 2 ^ 59
def prefixEnd_2567560 : Nat := 4983230072969 + 3 ^ 40 * 2567560 * 2
def baseEnd_2567560 : Nat := 1318392389258079643392013

theorem tailTrace_2567560 : CollatzResearch.WordTrace tailWord_2567560 prefixEnd_2567560 1318392389258079643392013 := by
  unfold tailWord_2567560
  simp only [CollatzResearch.WordTrace]
  refine ⟨46823303289088049590998067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62431071052117399454664089 46823303289088049590998067)
  ·
    refine ⟨70234954933632074386497101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46823303289088049590998067 70234954933632074386497101)
    ·
      refine ⟨26338108100112027894936413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70234954933632074386497101 26338108100112027894936413)
      ·
        refine ⟨9876790537542010460601155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26338108100112027894936413 9876790537542010460601155)
        ·
          refine ⟨14815185806313015690901733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9876790537542010460601155 14815185806313015690901733)
          ·
            refine ⟨2777847338683690442044075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14815185806313015690901733 2777847338683690442044075)
            ·
              refine ⟨4166771008025535663066113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2777847338683690442044075 4166771008025535663066113)
              ·
                refine ⟨3125078256019151747299585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4166771008025535663066113 3125078256019151747299585)
                ·
                  refine ⟨2343808692014363810474689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3125078256019151747299585 2343808692014363810474689)
                  ·
                    refine ⟨1757856519010772857856017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2343808692014363810474689 1757856519010772857856017)
                    ·
                      refine ⟨1318392389258079643392013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1757856519010772857856017 1318392389258079643392013)
                      ·
                        rfl

theorem cell23_2567560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_2567560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567560 prefixEnd_2567560 := by exact prefixLift 2567560
  have htrace : WordTrace (prefixWord ++ tailWord_2567560) baseStart_2567560 baseEnd_2567560 := by
    simpa [prefixWord, tailWord_2567560, baseEnd_2567560] using wordTrace_append hprefix tailTrace_2567560
  have hstable : (prefixWord ++ tailWord_2567560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567560).length < 2 ^ (prefixWord ++ tailWord_2567560).sum := by decide
  have hdescent : baseEnd_2567560 < baseStart_2567560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567566 : List Nat := [4, 1, 1, 4, 2, 1, 2, 1, 7]
def baseStart_2567566 : Nat := 118140960795 + 2567566 * 2 ^ 59
def prefixEnd_2567566 : Nat := 4983230072969 + 3 ^ 40 * 2567566 * 2
def baseEnd_2567566 : Nat := 146488385571334068879665

theorem tailTrace_2567566 : CollatzResearch.WordTrace tailWord_2567566 prefixEnd_2567566 146488385571334068879665 := by
  unfold tailWord_2567566
  simp only [CollatzResearch.WordTrace]
  refine ⟨11705853177019295275839319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62431216944102908137809701 11705853177019295275839319)
  ·
    refine ⟨17558779765528942913758979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11705853177019295275839319 17558779765528942913758979)
    ·
      refine ⟨26338169648293414370638469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17558779765528942913758979 26338169648293414370638469)
      ·
        refine ⟨4938406809055015194494713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26338169648293414370638469 4938406809055015194494713)
        ·
          refine ⟨3703805106791261395871035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4938406809055015194494713 3703805106791261395871035)
          ·
            refine ⟨5555707660186892093806553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3703805106791261395871035 5555707660186892093806553)
            ·
              refine ⟨4166780745140169070354915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5555707660186892093806553 4166780745140169070354915)
              ·
                refine ⟨6250171117710253605532373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4166780745140169070354915 6250171117710253605532373)
                ·
                  refine ⟨146488385571334068879665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6250171117710253605532373 146488385571334068879665)
                  ·
                    rfl

theorem cell23_2567566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 7].length) (baseStart_2567566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567566 prefixEnd_2567566 := by exact prefixLift 2567566
  have htrace : WordTrace (prefixWord ++ tailWord_2567566) baseStart_2567566 baseEnd_2567566 := by
    simpa [prefixWord, tailWord_2567566, baseEnd_2567566] using wordTrace_append hprefix tailTrace_2567566
  have hstable : (prefixWord ++ tailWord_2567566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567566).length < 2 ^ (prefixWord ++ tailWord_2567566).sum := by decide
  have hdescent : baseEnd_2567566 < baseStart_2567566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567599 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 1, 6, 2]
def baseStart_2567599 : Nat := 118140960795 + 2567599 * 2 ^ 59
def prefixEnd_2567599 : Nat := 4983230072969 + 3 ^ 40 * 2567599 * 2
def baseEnd_2567599 : Nat := 1318412415003604990804333

theorem tailTrace_2567599 : CollatzResearch.WordTrace tailWord_2567599 prefixEnd_2567599 1318412415003604990804333 := by
  unfold tailWord_2567599
  simp only [CollatzResearch.WordTrace]
  refine ⟨93648029025034808842665851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62432019350023205895110567 93648029025034808842665851)
  ·
    refine ⟨140472043537552213263998777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93648029025034808842665851 140472043537552213263998777)
    ·
      refine ⟨105354032653164159947999083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140472043537552213263998777 105354032653164159947999083)
      ·
        refine ⟨158031048979746239921998625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105354032653164159947999083 158031048979746239921998625)
        ·
          refine ⟨118523286734809679941498969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158031048979746239921998625 118523286734809679941498969)
          ·
            refine ⟨88892465051107259956124227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118523286734809679941498969 88892465051107259956124227)
            ·
              refine ⟨133338697576660889934186341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88892465051107259956124227 133338697576660889934186341)
              ·
                refine ⟨25001005795623916862659939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 133338697576660889934186341 25001005795623916862659939)
                ·
                  refine ⟨37501508693435875293989909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25001005795623916862659939 37501508693435875293989909)
                  ·
                    refine ⟨1757883220004806654405777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37501508693435875293989909 1757883220004806654405777)
                    ·
                      refine ⟨1318412415003604990804333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1757883220004806654405777 1318412415003604990804333)
                      ·
                        rfl

theorem cell23_2567599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 6, 2].length) (baseStart_2567599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567599 prefixEnd_2567599 := by exact prefixLift 2567599
  have htrace : WordTrace (prefixWord ++ tailWord_2567599) baseStart_2567599 baseEnd_2567599 := by
    simpa [prefixWord, tailWord_2567599, baseEnd_2567599] using wordTrace_append hprefix tailTrace_2567599
  have hstable : (prefixWord ++ tailWord_2567599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567599).length < 2 ^ (prefixWord ++ tailWord_2567599).sum := by decide
  have hdescent : baseEnd_2567599 < baseStart_2567599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567619 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 4, 2, 3]
def baseStart_2567619 : Nat := 118140960795 + 2567619 * 2 ^ 59
def prefixEnd_2567619 : Nat := 4983230072969 + 3 ^ 40 * 2567619 * 2
def baseEnd_2567619 : Nat := 1318422684616694912554241

theorem tailTrace_2567619 : CollatzResearch.WordTrace tailWord_2567619 prefixEnd_2567619 1318422684616694912554241 := by
  unfold tailWord_2567619
  simp only [CollatzResearch.WordTrace]
  refine ⟨93648758484962352258393911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62432505656641568172262607 93648758484962352258393911)
  ·
    refine ⟨140473137727443528387590867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93648758484962352258393911 140473137727443528387590867)
    ·
      refine ⟨210709706591165292581386301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140473137727443528387590867 210709706591165292581386301)
      ·
        refine ⟨79016139971686984718019863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210709706591165292581386301 79016139971686984718019863)
        ·
          refine ⟨118524209957530477077029795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79016139971686984718019863 118524209957530477077029795)
          ·
            refine ⟨177786314936295715615544693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118524209957530477077029795 177786314936295715615544693)
            ·
              refine ⟨16667467025277723338957315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 177786314936295715615544693 16667467025277723338957315)
              ·
                refine ⟨25001200537916585008435973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16667467025277723338957315 25001200537916585008435973)
                ·
                  refine ⟨4687725100859359689081745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25001200537916585008435973 4687725100859359689081745)
                  ·
                    refine ⟨3515793825644519766811309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4687725100859359689081745 3515793825644519766811309)
                    ·
                      refine ⟨1318422684616694912554241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3515793825644519766811309 1318422684616694912554241)
                      ·
                        rfl

theorem cell23_2567619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 2, 3].length) (baseStart_2567619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567619 prefixEnd_2567619 := by exact prefixLift 2567619
  have htrace : WordTrace (prefixWord ++ tailWord_2567619) baseStart_2567619 baseEnd_2567619 := by
    simpa [prefixWord, tailWord_2567619, baseEnd_2567619] using wordTrace_append hprefix tailTrace_2567619
  have hstable : (prefixWord ++ tailWord_2567619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567619).length < 2 ^ (prefixWord ++ tailWord_2567619).sum := by decide
  have hdescent : baseEnd_2567619 < baseStart_2567619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567626 : List Nat := [3, 1, 2, 1, 2, 3, 3, 1, 3, 4]
def baseStart_2567626 : Nat := 118140960795 + 2567626 * 2 ^ 59
def prefixEnd_2567626 : Nat := 4983230072969 + 3 ^ 40 * 2567626 * 2
def baseEnd_2567626 : Nat := 439475426327092128388903

theorem tailTrace_2567626 : CollatzResearch.WordTrace tailWord_2567626 prefixEnd_2567626 439475426327092128388903 := by
  unfold tailWord_2567626
  simp only [CollatzResearch.WordTrace]
  refine ⟨23412253448984248113474683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62432675863957994969265821 23412253448984248113474683)
  ·
    refine ⟨35118380173476372170212025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23412253448984248113474683 35118380173476372170212025)
    ·
      refine ⟨26338785130107279127659019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35118380173476372170212025 26338785130107279127659019)
      ·
        refine ⟨39508177695160918691488529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26338785130107279127659019 39508177695160918691488529)
        ·
          refine ⟨29631133271370689018616397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39508177695160918691488529 29631133271370689018616397)
          ·
            refine ⟨11111674976764008381981149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29631133271370689018616397 11111674976764008381981149)
            ·
              refine ⟨4166878116286503143242931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11111674976764008381981149 4166878116286503143242931)
              ·
                refine ⟨6250317174429754714864397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4166878116286503143242931 6250317174429754714864397)
                ·
                  refine ⟨2343868940411158018074149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6250317174429754714864397 2343868940411158018074149)
                  ·
                    refine ⟨439475426327092128388903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2343868940411158018074149 439475426327092128388903)
                    ·
                      rfl

theorem cell23_2567626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_2567626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567626 prefixEnd_2567626 := by exact prefixLift 2567626
  have htrace : WordTrace (prefixWord ++ tailWord_2567626) baseStart_2567626 baseEnd_2567626 := by
    simpa [prefixWord, tailWord_2567626, baseEnd_2567626] using wordTrace_append hprefix tailTrace_2567626
  have hstable : (prefixWord ++ tailWord_2567626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567626).length < 2 ^ (prefixWord ++ tailWord_2567626).sum := by decide
  have hdescent : baseEnd_2567626 < baseStart_2567626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567653 : List Nat := [1, 3, 1, 5, 1, 2, 2, 1, 2, 2, 3]
def baseStart_2567653 : Nat := 118140960795 + 2567653 * 2 ^ 59
def prefixEnd_2567653 : Nat := 4983230072969 + 3 ^ 40 * 2567653 * 2
def baseEnd_2567653 : Nat := 1318440142958947779529085

theorem tailTrace_2567653 : CollatzResearch.WordTrace tailWord_2567653 prefixEnd_2567653 1318440142958947779529085 := by
  unfold tailWord_2567653
  simp only [CollatzResearch.WordTrace]
  refine ⟨93649998566839176065131613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62433332377892784043421075 93649998566839176065131613)
  ·
    refine ⟨35118749462564691024424355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93649998566839176065131613 35118749462564691024424355)
    ·
      refine ⟨52678124193847036536636533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35118749462564691024424355 52678124193847036536636533)
      ·
        refine ⟨4938574143173159675309675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52678124193847036536636533 4938574143173159675309675)
        ·
          refine ⟨7407861214759739512964513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4938574143173159675309675 7407861214759739512964513)
          ·
            refine ⟨5555895911069804634723385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7407861214759739512964513 5555895911069804634723385)
            ·
              refine ⟨4166921933302353476042539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5555895911069804634723385 4166921933302353476042539)
              ·
                refine ⟨6250382899953530214063809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4166921933302353476042539 6250382899953530214063809)
                ·
                  refine ⟨4687787174965147660547857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6250382899953530214063809 4687787174965147660547857)
                  ·
                    refine ⟨3515840381223860745410893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4687787174965147660547857 3515840381223860745410893)
                    ·
                      refine ⟨1318440142958947779529085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3515840381223860745410893 1318440142958947779529085)
                      ·
                        rfl

theorem cell23_2567653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_2567653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567653 prefixEnd_2567653 := by exact prefixLift 2567653
  have htrace : WordTrace (prefixWord ++ tailWord_2567653) baseStart_2567653 baseEnd_2567653 := by
    simpa [prefixWord, tailWord_2567653, baseEnd_2567653] using wordTrace_append hprefix tailTrace_2567653
  have hstable : (prefixWord ++ tailWord_2567653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567653).length < 2 ^ (prefixWord ++ tailWord_2567653).sum := by decide
  have hdescent : baseEnd_2567653 < baseStart_2567653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567689 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 5, 1, 4]
def baseStart_2567689 : Nat := 118140960795 + 2567689 * 2 ^ 59
def prefixEnd_2567689 : Nat := 4983230072969 + 3 ^ 40 * 2567689 * 2
def baseEnd_2567689 : Nat := 1318458628262509638678919

theorem tailTrace_2567689 : CollatzResearch.WordTrace tailWord_2567689 prefixEnd_2567689 1318458628262509638678919 := by
  unfold tailWord_2567689
  simp only [CollatzResearch.WordTrace]
  refine ⟨93651311594708754213442121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62434207729805836142294747 93651311594708754213442121)
  ·
    refine ⟨70238483696031565660081591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93651311594708754213442121 70238483696031565660081591)
    ·
      refine ⟨105357725544047348490122387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70238483696031565660081591 105357725544047348490122387)
      ·
        refine ⟨158036588316071022735183581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105357725544047348490122387 158036588316071022735183581)
        ·
          refine ⟨59263720618526633525693843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158036588316071022735183581 59263720618526633525693843)
          ·
            refine ⟨88895580927789950288540765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59263720618526633525693843 88895580927789950288540765)
            ·
              refine ⟨33335842847921231358202787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88895580927789950288540765 33335842847921231358202787)
              ·
                refine ⟨50003764271881847037304181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33335842847921231358202787 50003764271881847037304181)
                ·
                  refine ⟨4687852900488923159747267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50003764271881847037304181 4687852900488923159747267)
                  ·
                    refine ⟨7031779350733384739620901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4687852900488923159747267 7031779350733384739620901)
                    ·
                      refine ⟨1318458628262509638678919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7031779350733384739620901 1318458628262509638678919)
                      ·
                        rfl

theorem cell23_2567689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 1, 4].length) (baseStart_2567689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567689 prefixEnd_2567689 := by exact prefixLift 2567689
  have htrace : WordTrace (prefixWord ++ tailWord_2567689) baseStart_2567689 baseEnd_2567689 := by
    simpa [prefixWord, tailWord_2567689, baseEnd_2567689] using wordTrace_append hprefix tailTrace_2567689
  have hstable : (prefixWord ++ tailWord_2567689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567689).length < 2 ^ (prefixWord ++ tailWord_2567689).sum := by decide
  have hdescent : baseEnd_2567689 < baseStart_2567689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567699 : List Nat := [1, 1, 1, 2, 1, 6, 1, 3, 1, 6]
def baseStart_2567699 : Nat := 118140960795 + 2567699 * 2 ^ 59
def prefixEnd_2567699 : Nat := 4983230072969 + 3 ^ 40 * 2567699 * 2
def baseEnd_2567699 : Nat := 439487921023018199851291

theorem tailTrace_2567699 : CollatzResearch.WordTrace tailWord_2567699 prefixEnd_2567699 439487921023018199851291 := by
  unfold tailWord_2567699
  simp only [CollatzResearch.WordTrace]
  refine ⟨93651676324672525921306151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62434450883115017280870767 93651676324672525921306151)
  ·
    refine ⟨140477514487008788881959227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93651676324672525921306151 140477514487008788881959227)
    ·
      refine ⟨210716271730513183322938841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140477514487008788881959227 210716271730513183322938841)
      ·
        refine ⟨158037203797884887492204131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210716271730513183322938841 158037203797884887492204131)
        ·
          refine ⟨237055805696827331238306197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158037203797884887492204131 237055805696827331238306197)
          ·
            refine ⟨11111990892038781151795603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 237055805696827331238306197 11111990892038781151795603)
            ·
              refine ⟨16667986338058171727693405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11111990892038781151795603 16667986338058171727693405)
              ·
                refine ⟨6250494876771814397885027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16667986338058171727693405 6250494876771814397885027)
                ·
                  refine ⟨9375742315157721596827541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6250494876771814397885027 9375742315157721596827541)
                  ·
                    refine ⟨439487921023018199851291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9375742315157721596827541 439487921023018199851291)
                    ·
                      rfl

theorem cell23_2567699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 6].length) (baseStart_2567699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567699 prefixEnd_2567699 := by exact prefixLift 2567699
  have htrace : WordTrace (prefixWord ++ tailWord_2567699) baseStart_2567699 baseEnd_2567699 := by
    simpa [prefixWord, tailWord_2567699, baseEnd_2567699] using wordTrace_append hprefix tailTrace_2567699
  have hstable : (prefixWord ++ tailWord_2567699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567699).length < 2 ^ (prefixWord ++ tailWord_2567699).sum := by decide
  have hdescent : baseEnd_2567699 < baseStart_2567699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567706 : List Nat := [3, 1, 1, 3, 1, 1, 1, 6, 1, 1, 4]
def baseStart_2567706 : Nat := 118140960795 + 2567706 * 2 ^ 59
def prefixEnd_2567706 : Nat := 4983230072969 + 3 ^ 40 * 2567706 * 2
def baseEnd_2567706 : Nat := 1318467357433636072166341

theorem tailTrace_2567706 : CollatzResearch.WordTrace tailWord_2567706 prefixEnd_2567706 1318467357433636072166341 := by
  unfold tailWord_2567706
  simp only [CollatzResearch.WordTrace]
  refine ⟨23412982908911791529202743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62434621090431444077873981 23412982908911791529202743)
  ·
    refine ⟨35119474363367687293804115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23412982908911791529202743 35119474363367687293804115)
    ·
      refine ⟨52679211545051530940706173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35119474363367687293804115 52679211545051530940706173)
      ·
        refine ⟨19754704329394324102764815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52679211545051530940706173 19754704329394324102764815)
        ·
          refine ⟨29632056494091486154147223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19754704329394324102764815 29632056494091486154147223)
          ·
            refine ⟨44448084741137229231220835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29632056494091486154147223 44448084741137229231220835)
            ·
              refine ⟨66672127111705843846831253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44448084741137229231220835 66672127111705843846831253)
              ·
                refine ⟨3125255958361211430320215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66672127111705843846831253 3125255958361211430320215)
                ·
                  refine ⟨4687883937541817145480323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3125255958361211430320215 4687883937541817145480323)
                  ·
                    refine ⟨7031825906312725718220485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4687883937541817145480323 7031825906312725718220485)
                    ·
                      refine ⟨1318467357433636072166341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7031825906312725718220485 1318467357433636072166341)
                      ·
                        rfl

theorem cell23_2567706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_2567706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567706 prefixEnd_2567706 := by exact prefixLift 2567706
  have htrace : WordTrace (prefixWord ++ tailWord_2567706) baseStart_2567706 baseEnd_2567706 := by
    simpa [prefixWord, tailWord_2567706, baseEnd_2567706] using wordTrace_append hprefix tailTrace_2567706
  have hstable : (prefixWord ++ tailWord_2567706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567706).length < 2 ^ (prefixWord ++ tailWord_2567706).sum := by decide
  have hdescent : baseEnd_2567706 < baseStart_2567706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567733 : List Nat := [1, 3, 3, 1, 1, 3, 3, 2, 2, 4]
def baseStart_2567733 : Nat := 118140960795 + 2567733 * 2 ^ 59
def prefixEnd_2567733 : Nat := 4983230072969 + 3 ^ 40 * 2567733 * 2
def baseEnd_2567733 : Nat := 439493740470435822176239

theorem tailTrace_2567733 : CollatzResearch.WordTrace tailWord_2567733 prefixEnd_2567733 439493740470435822176239 := by
  unfold tailWord_2567733
  simp only [CollatzResearch.WordTrace]
  refine ⟨93652916406549349728043853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62435277604366233152029235 93652916406549349728043853)
  ·
    refine ⟨35119843652456006148016445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93652916406549349728043853 35119843652456006148016445)
    ·
      refine ⟨13169941369671002305506167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35119843652456006148016445 13169941369671002305506167)
      ·
        refine ⟨19754912054506503458259251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13169941369671002305506167 19754912054506503458259251)
        ·
          refine ⟨29632368081759755187388877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19754912054506503458259251 29632368081759755187388877)
          ·
            refine ⟨11112138030659908195270829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29632368081759755187388877 11112138030659908195270829)
            ·
              refine ⟨4167051761497465573226561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11112138030659908195270829 4167051761497465573226561)
              ·
                refine ⟨3125288821123099179919921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4167051761497465573226561 3125288821123099179919921)
                ·
                  refine ⟨2343966615842324384939941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3125288821123099179919921 2343966615842324384939941)
                  ·
                    refine ⟨439493740470435822176239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2343966615842324384939941 439493740470435822176239)
                    ·
                      rfl

theorem cell23_2567733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_2567733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567733 prefixEnd_2567733 := by exact prefixLift 2567733
  have htrace : WordTrace (prefixWord ++ tailWord_2567733) baseStart_2567733 baseEnd_2567733 := by
    simpa [prefixWord, tailWord_2567733, baseEnd_2567733] using wordTrace_append hprefix tailTrace_2567733
  have hstable : (prefixWord ++ tailWord_2567733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567733).length < 2 ^ (prefixWord ++ tailWord_2567733).sum := by decide
  have hdescent : baseEnd_2567733 < baseStart_2567733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567799 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 5]
def baseStart_2567799 : Nat := 118140960795 + 2567799 * 2 ^ 59
def prefixEnd_2567799 : Nat := 4983230072969 + 3 ^ 40 * 2567799 * 2
def baseEnd_2567799 : Nat := 1318515111134504208303413

theorem tailTrace_2567799 : CollatzResearch.WordTrace tailWord_2567799 prefixEnd_2567799 1318515111134504208303413 := by
  unfold tailWord_2567799
  simp only [CollatzResearch.WordTrace]
  refine ⟨93655323624310242999946451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62436882416206828666630967 93655323624310242999946451)
  ·
    refine ⟨140482985436465364499919677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93655323624310242999946451 140482985436465364499919677)
    ·
      refine ⟨52681119538674511687469879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140482985436465364499919677 52681119538674511687469879)
      ·
        refine ⟨79021679308011767531204819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52681119538674511687469879 79021679308011767531204819)
        ·
          refine ⟨118532518962017651296807229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79021679308011767531204819 118532518962017651296807229)
          ·
            refine ⟨44449694610756619236302711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118532518962017651296807229 44449694610756619236302711)
            ·
              refine ⟨66674541916134928854454067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44449694610756619236302711 66674541916134928854454067)
              ·
                refine ⟨100011812874202393281681101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66674541916134928854454067 100011812874202393281681101)
                ·
                  refine ⟨37504429827825897480630413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100011812874202393281681101 37504429827825897480630413)
                  ·
                    refine ⟨14064161185434711555236405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37504429827825897480630413 14064161185434711555236405)
                    ·
                      refine ⟨1318515111134504208303413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14064161185434711555236405 1318515111134504208303413)
                      ·
                        rfl

theorem cell23_2567799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_2567799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567799 prefixEnd_2567799 := by exact prefixLift 2567799
  have htrace : WordTrace (prefixWord ++ tailWord_2567799) baseStart_2567799 baseEnd_2567799 := by
    simpa [prefixWord, tailWord_2567799, baseEnd_2567799] using wordTrace_append hprefix tailTrace_2567799
  have hstable : (prefixWord ++ tailWord_2567799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567799).length < 2 ^ (prefixWord ++ tailWord_2567799).sum := by decide
  have hdescent : baseEnd_2567799 < baseStart_2567799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567813 : List Nat := [1, 3, 1, 1, 4, 1, 2, 3, 1, 4, 2]
def baseStart_2567813 : Nat := 118140960795 + 2567813 * 2 ^ 59
def prefixEnd_2567813 : Nat := 4983230072969 + 3 ^ 40 * 2567813 * 2
def baseEnd_2567813 : Nat := 1318522299863667153528349

theorem tailTrace_2567813 : CollatzResearch.WordTrace tailWord_2567813 prefixEnd_2567813 1318522299863667153528349 := by
  unfold tailWord_2567813
  simp only [CollatzResearch.WordTrace]
  refine ⟨93655834246259523390956093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62437222830839682260637395 93655834246259523390956093)
  ·
    refine ⟨35120937842347321271608535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93655834246259523390956093 35120937842347321271608535)
    ·
      refine ⟨52681406763520981907412803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35120937842347321271608535 52681406763520981907412803)
      ·
        refine ⟨79022110145281472861119205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52681406763520981907412803 79022110145281472861119205)
        ·
          refine ⟨14816645652240276161459851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79022110145281472861119205 14816645652240276161459851)
          ·
            refine ⟨22224968478360414242189777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14816645652240276161459851 22224968478360414242189777)
            ·
              refine ⟨16668726358770310681642333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22224968478360414242189777 16668726358770310681642333)
              ·
                refine ⟨6250772384538866505615875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16668726358770310681642333 6250772384538866505615875)
                ·
                  refine ⟨9376158576808299758423813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6250772384538866505615875 9376158576808299758423813)
                  ·
                    refine ⟨1758029733151556204704465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9376158576808299758423813 1758029733151556204704465)
                    ·
                      refine ⟨1318522299863667153528349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1758029733151556204704465 1318522299863667153528349)
                      ·
                        rfl

theorem cell23_2567813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 4, 2].length) (baseStart_2567813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567813 prefixEnd_2567813 := by exact prefixLift 2567813
  have htrace : WordTrace (prefixWord ++ tailWord_2567813) baseStart_2567813 baseEnd_2567813 := by
    simpa [prefixWord, tailWord_2567813, baseEnd_2567813] using wordTrace_append hprefix tailTrace_2567813
  have hstable : (prefixWord ++ tailWord_2567813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567813).length < 2 ^ (prefixWord ++ tailWord_2567813).sum := by decide
  have hdescent : baseEnd_2567813 < baseStart_2567813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567819 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 9]
def baseStart_2567819 : Nat := 118140960795 + 2567819 * 2 ^ 59
def prefixEnd_2567819 : Nat := 4983230072969 + 3 ^ 40 * 2567819 * 2
def baseEnd_2567819 : Nat := 146502820083066014450369

theorem tailTrace_2567819 : CollatzResearch.WordTrace tailWord_2567819 prefixEnd_2567819 146502820083066014450369 := by
  unfold tailWord_2567819
  simp only [CollatzResearch.WordTrace]
  refine ⟨93656053084237786415674511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62437368722825190943783007 93656053084237786415674511)
  ·
    refine ⟨140484079626356679623511767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93656053084237786415674511 140484079626356679623511767)
    ·
      refine ⟨210726119439535019435267651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140484079626356679623511767 210726119439535019435267651)
      ·
        refine ⟨316089179159302529152901477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210726119439535019435267651 316089179159302529152901477)
        ·
          refine ⟨59266721092369224216169027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 316089179159302529152901477 59266721092369224216169027)
          ·
            refine ⟨88900081638553836324253541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59266721092369224216169027 88900081638553836324253541)
            ·
              refine ⟨16668765307228844310797539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88900081638553836324253541 16668765307228844310797539)
              ·
                refine ⟨25003147960843266466196309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16668765307228844310797539 25003147960843266466196309)
                ·
                  refine ⟨146502820083066014450369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25003147960843266466196309 146502820083066014450369)
                  ·
                    rfl

theorem cell23_2567819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 9].length) (baseStart_2567819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567819 prefixEnd_2567819 := by exact prefixLift 2567819
  have htrace : WordTrace (prefixWord ++ tailWord_2567819) baseStart_2567819 baseEnd_2567819 := by
    simpa [prefixWord, tailWord_2567819, baseEnd_2567819] using wordTrace_append hprefix tailTrace_2567819
  have hstable : (prefixWord ++ tailWord_2567819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567819).length < 2 ^ (prefixWord ++ tailWord_2567819).sum := by decide
  have hdescent : baseEnd_2567819 < baseStart_2567819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567863 : List Nat := [1, 1, 3, 1, 5, 2, 1, 1, 2, 3, 3]
def baseStart_2567863 : Nat := 118140960795 + 2567863 * 2 ^ 59
def prefixEnd_2567863 : Nat := 4983230072969 + 3 ^ 40 * 2567863 * 2
def baseEnd_2567863 : Nat := 1318547973896391957903119

theorem tailTrace_2567863 : CollatzResearch.WordTrace tailWord_2567863 prefixEnd_2567863 1318547973896391957903119 := by
  unfold tailWord_2567863
  simp only [CollatzResearch.WordTrace]
  refine ⟨93657657896078381930276243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62438438597385587953517495 93657657896078381930276243)
  ·
    refine ⟨140486486844117572895414365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93657657896078381930276243 140486486844117572895414365)
    ·
      refine ⟨52682432566544089835780387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140486486844117572895414365 52682432566544089835780387)
      ·
        refine ⟨79023648849816134753670581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52682432566544089835780387 79023648849816134753670581)
        ·
          refine ⟨7408467079670262633156617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79023648849816134753670581 7408467079670262633156617)
          ·
            refine ⟨5556350309752696974867463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7408467079670262633156617 5556350309752696974867463)
            ·
              refine ⟨8334525464629045462301195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5556350309752696974867463 8334525464629045462301195)
              ·
                refine ⟨12501788196943568193451793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8334525464629045462301195 12501788196943568193451793)
                ·
                  refine ⟨9376341147707676145088845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12501788196943568193451793 9376341147707676145088845)
                  ·
                    refine ⟨3516127930390378554408317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9376341147707676145088845 3516127930390378554408317)
                    ·
                      refine ⟨1318547973896391957903119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3516127930390378554408317 1318547973896391957903119)
                      ·
                        rfl

theorem cell23_2567863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 3, 3].length) (baseStart_2567863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567863 prefixEnd_2567863 := by exact prefixLift 2567863
  have htrace : WordTrace (prefixWord ++ tailWord_2567863) baseStart_2567863 baseEnd_2567863 := by
    simpa [prefixWord, tailWord_2567863, baseEnd_2567863] using wordTrace_append hprefix tailTrace_2567863
  have hstable : (prefixWord ++ tailWord_2567863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567863).length < 2 ^ (prefixWord ++ tailWord_2567863).sum := by decide
  have hdescent : baseEnd_2567863 < baseStart_2567863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567903 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 4, 4, 2]
def baseStart_2567903 : Nat := 118140960795 + 2567903 * 2 ^ 59
def prefixEnd_2567903 : Nat := 4983230072969 + 3 ^ 40 * 2567903 * 2
def baseEnd_2567903 : Nat := 1318568513122571801402935

theorem tailTrace_2567903 : CollatzResearch.WordTrace tailWord_2567903 prefixEnd_2567903 1318568513122571801402935 := by
  unfold tailWord_2567903
  simp only [CollatzResearch.WordTrace]
  refine ⟨93659116815933468761732363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62439411210622312507821575 93659116815933468761732363)
  ·
    refine ⟨140488675223900203142598545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93659116815933468761732363 140488675223900203142598545)
    ·
      refine ⟨105366506417925152356948909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140488675223900203142598545 105366506417925152356948909)
      ·
        refine ⟨39512439906721932133855841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105366506417925152356948909 39512439906721932133855841)
        ·
          refine ⟨29634329930041449100391881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39512439906721932133855841 29634329930041449100391881)
          ·
            refine ⟨22225747447531086825293911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29634329930041449100391881 22225747447531086825293911)
            ·
              refine ⟨33338621171296630237940867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22225747447531086825293911 33338621171296630237940867)
              ·
                refine ⟨50007931756944945356911301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33338621171296630237940867 50007931756944945356911301)
                ·
                  refine ⟨9376487204427177254420869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50007931756944945356911301 9376487204427177254420869)
                  ·
                    refine ⟨1758091350830095735203913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9376487204427177254420869 1758091350830095735203913)
                    ·
                      refine ⟨1318568513122571801402935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1758091350830095735203913 1318568513122571801402935)
                      ·
                        rfl

theorem cell23_2567903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 4, 2].length) (baseStart_2567903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567903 prefixEnd_2567903 := by exact prefixLift 2567903
  have htrace : WordTrace (prefixWord ++ tailWord_2567903) baseStart_2567903 baseEnd_2567903 := by
    simpa [prefixWord, tailWord_2567903, baseEnd_2567903] using wordTrace_append hprefix tailTrace_2567903
  have hstable : (prefixWord ++ tailWord_2567903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567903).length < 2 ^ (prefixWord ++ tailWord_2567903).sum := by decide
  have hdescent : baseEnd_2567903 < baseStart_2567903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2567997 : List Nat := [1, 4, 1, 4, 1, 1, 1, 3, 2, 3, 2]
def baseStart_2567997 : Nat := 118140960795 + 2567997 * 2 ^ 59
def prefixEnd_2567997 : Nat := 4983230072969 + 3 ^ 40 * 2567997 * 2
def baseEnd_2567997 : Nat := 1318616780304094433627503

theorem tailTrace_2567997 : CollatzResearch.WordTrace tailWord_2567997 prefixEnd_2567997 1318616780304094433627503 := by
  unfold tailWord_2567997
  simp only [CollatzResearch.WordTrace]
  refine ⟨93662545277592922815654245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62441696851728615210436163 93662545277592922815654245)
  ·
    refine ⟨17561727239548673027935171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93662545277592922815654245 17561727239548673027935171)
    ·
      refine ⟨26342590859323009541902757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17561727239548673027935171 26342590859323009541902757)
      ·
        refine ⟨4939235786123064289106767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26342590859323009541902757 4939235786123064289106767)
        ·
          refine ⟨7408853679184596433660151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4939235786123064289106767 7408853679184596433660151)
          ·
            refine ⟨11113280518776894650490227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7408853679184596433660151 11113280518776894650490227)
            ·
              refine ⟨16669920778165341975735341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11113280518776894650490227 16669920778165341975735341)
              ·
                refine ⟨6251220291812003240900753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16669920778165341975735341 6251220291812003240900753)
                ·
                  refine ⟨4688415218859002430675565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6251220291812003240900753 4688415218859002430675565)
                  ·
                    refine ⟨1758155707072125911503337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4688415218859002430675565 1758155707072125911503337)
                    ·
                      refine ⟨1318616780304094433627503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1758155707072125911503337 1318616780304094433627503)
                      ·
                        rfl

theorem cell23_2567997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_2567997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2567997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2567997 prefixEnd_2567997 := by exact prefixLift 2567997
  have htrace : WordTrace (prefixWord ++ tailWord_2567997) baseStart_2567997 baseEnd_2567997 := by
    simpa [prefixWord, tailWord_2567997, baseEnd_2567997] using wordTrace_append hprefix tailTrace_2567997
  have hstable : (prefixWord ++ tailWord_2567997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2567997).length < 2 ^ (prefixWord ++ tailWord_2567997).sum := by decide
  have hdescent : baseEnd_2567997 < baseStart_2567997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2567997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568003 : List Nat := [1, 1, 1, 3, 1, 6, 1, 2, 1, 6]
def baseStart_2568003 : Nat := 118140960795 + 2568003 * 2 ^ 59
def prefixEnd_2568003 : Nat := 4983230072969 + 3 ^ 40 * 2568003 * 2
def baseEnd_2568003 : Nat := 439539953729340470050825

theorem tailTrace_2568003 : CollatzResearch.WordTrace tailWord_2568003 prefixEnd_2568003 439539953729340470050825 := by
  unfold tailWord_2568003
  simp only [CollatzResearch.WordTrace]
  refine ⟨93662764115571185840372663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62441842743714123893581775 93662764115571185840372663)
  ·
    refine ⟨140494146173356778760558995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93662764115571185840372663 140494146173356778760558995)
    ·
      refine ⟨210741219260035168140838493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140494146173356778760558995 210741219260035168140838493)
      ·
        refine ⟨79027957222513188052814435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210741219260035168140838493 79027957222513188052814435)
        ·
          refine ⟨118541935833769782079221653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79027957222513188052814435 118541935833769782079221653)
          ·
            refine ⟨5556653242207958534963515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 118541935833769782079221653 5556653242207958534963515)
            ·
              refine ⟨8334979863311937802445273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5556653242207958534963515 8334979863311937802445273)
              ·
                refine ⟨6251234897483953351833955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8334979863311937802445273 6251234897483953351833955)
                ·
                  refine ⟨9376852346225930027750933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6251234897483953351833955 9376852346225930027750933)
                  ·
                    refine ⟨439539953729340470050825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9376852346225930027750933 439539953729340470050825)
                    ·
                      rfl

theorem cell23_2568003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 6].length) (baseStart_2568003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568003 prefixEnd_2568003 := by exact prefixLift 2568003
  have htrace : WordTrace (prefixWord ++ tailWord_2568003) baseStart_2568003 baseEnd_2568003 := by
    simpa [prefixWord, tailWord_2568003, baseEnd_2568003] using wordTrace_append hprefix tailTrace_2568003
  have hstable : (prefixWord ++ tailWord_2568003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568003).length < 2 ^ (prefixWord ++ tailWord_2568003).sum := by decide
  have hdescent : baseEnd_2568003 < baseStart_2568003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568021 : List Nat := [1, 3, 2, 2, 2, 4, 2, 2, 1, 1, 3]
def baseStart_2568021 : Nat := 118140960795 + 2568021 * 2 ^ 59
def prefixEnd_2568021 : Nat := 4983230072969 + 3 ^ 40 * 2568021 * 2
def baseEnd_2568021 : Nat := 1318629103839802339727393

theorem tailTrace_2568021 : CollatzResearch.WordTrace tailWord_2568021 prefixEnd_2568021 1318629103839802339727393 := by
  unfold tailWord_2568021
  simp only [CollatzResearch.WordTrace]
  refine ⟨93663420629505974914527917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62442280419670649943018611 93663420629505974914527917)
  ·
    refine ⟨35123782736064740592947969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93663420629505974914527917 35123782736064740592947969)
    ·
      refine ⟨26342837052048555444710977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35123782736064740592947969 26342837052048555444710977)
      ·
        refine ⟨19757127789036416583533233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26342837052048555444710977 19757127789036416583533233)
        ·
          refine ⟨14817845841777312437649925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19757127789036416583533233 14817845841777312437649925)
          ·
            refine ⟨2778346095333246082059361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14817845841777312437649925 2778346095333246082059361)
            ·
              refine ⟨2083759571499934561544521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2778346095333246082059361 2083759571499934561544521)
              ·
                refine ⟨1562819678624950921158391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2083759571499934561544521 1562819678624950921158391)
                ·
                  refine ⟨2344229517937426381737587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1562819678624950921158391 2344229517937426381737587)
                  ·
                    refine ⟨3516344276906139572606381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2344229517937426381737587 3516344276906139572606381)
                    ·
                      refine ⟨1318629103839802339727393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3516344276906139572606381 1318629103839802339727393)
                      ·
                        rfl

theorem cell23_2568021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_2568021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568021 prefixEnd_2568021 := by exact prefixLift 2568021
  have htrace : WordTrace (prefixWord ++ tailWord_2568021) baseStart_2568021 baseEnd_2568021 := by
    simpa [prefixWord, tailWord_2568021, baseEnd_2568021] using wordTrace_append hprefix tailTrace_2568021
  have hstable : (prefixWord ++ tailWord_2568021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568021).length < 2 ^ (prefixWord ++ tailWord_2568021).sum := by decide
  have hdescent : baseEnd_2568021 < baseStart_2568021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568040 : List Nat := [2, 1, 4, 2, 1, 1, 4, 1, 1, 2, 4]
def baseStart_2568040 : Nat := 118140960795 + 2568040 * 2 ^ 59
def prefixEnd_2568040 : Nat := 4983230072969 + 3 ^ 40 * 2568040 * 2
def baseEnd_2568040 : Nat := 1318638859972237765389805

theorem tailTrace_2568040 : CollatzResearch.WordTrace tailWord_2568040 prefixEnd_2568040 1318638859972237765389805 := by
  unfold tailWord_2568040
  simp only [CollatzResearch.WordTrace]
  refine ⟨46832056808218570579734787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62442742410958094106313049 46832056808218570579734787)
  ·
    refine ⟨70248085212327855869602181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46832056808218570579734787 70248085212327855869602181)
    ·
      refine ⟨13171515977311472975550409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70248085212327855869602181 13171515977311472975550409)
      ·
        refine ⟨9878636982983604731662807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13171515977311472975550409 9878636982983604731662807)
        ·
          refine ⟨14817955474475407097494211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9878636982983604731662807 14817955474475407097494211)
          ·
            refine ⟨22226933211713110646241317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14817955474475407097494211 22226933211713110646241317)
            ·
              refine ⟨4167549977196208246170247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22226933211713110646241317 4167549977196208246170247)
              ·
                refine ⟨6251324965794312369255371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4167549977196208246170247 6251324965794312369255371)
                ·
                  refine ⟨9376987448691468553883057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6251324965794312369255371 9376987448691468553883057)
                  ·
                    refine ⟨7032740586518601415412293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9376987448691468553883057 7032740586518601415412293)
                    ·
                      refine ⟨1318638859972237765389805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7032740586518601415412293 1318638859972237765389805)
                      ·
                        rfl

theorem cell23_2568040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_2568040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568040 prefixEnd_2568040 := by exact prefixLift 2568040
  have htrace : WordTrace (prefixWord ++ tailWord_2568040) baseStart_2568040 baseEnd_2568040 := by
    simpa [prefixWord, tailWord_2568040, baseEnd_2568040] using wordTrace_append hprefix tailTrace_2568040
  have hstable : (prefixWord ++ tailWord_2568040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568040).length < 2 ^ (prefixWord ++ tailWord_2568040).sum := by decide
  have hdescent : baseEnd_2568040 < baseStart_2568040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568140 : List Nat := [2, 2, 1, 4, 1, 2, 3, 1, 7]
def baseStart_2568140 : Nat := 118140960795 + 2568140 * 2 ^ 59
def prefixEnd_2568140 : Nat := 4983230072969 + 3 ^ 40 * 2568140 * 2
def baseEnd_2568140 : Nat := 146521134226409708237705

theorem tailTrace_2568140 : CollatzResearch.WordTrace tailWord_2568140 prefixEnd_2568140 146521134226409708237705 := by
  unfold tailWord_2568140
  simp only [CollatzResearch.WordTrace]
  refine ⟨46833880458037429119054937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62445173944049905492073249 46833880458037429119054937)
  ·
    refine ⟨35125410343528071839291203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46833880458037429119054937 35125410343528071839291203)
    ·
      refine ⟨52688115515292107758936805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35125410343528071839291203 52688115515292107758936805)
      ·
        refine ⟨9879021659117270204800651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52688115515292107758936805 9879021659117270204800651)
        ·
          refine ⟨14818532488675905307200977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9879021659117270204800651 14818532488675905307200977)
          ·
            refine ⟨11113899366506928980400733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14818532488675905307200977 11113899366506928980400733)
            ·
              refine ⟨4167712262440098367650275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11113899366506928980400733 4167712262440098367650275)
              ·
                refine ⟨6251568393660147551475413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4167712262440098367650275 6251568393660147551475413)
                ·
                  refine ⟨146521134226409708237705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6251568393660147551475413 146521134226409708237705)
                  ·
                    rfl

theorem cell23_2568140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 7].length) (baseStart_2568140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568140 prefixEnd_2568140 := by exact prefixLift 2568140
  have htrace : WordTrace (prefixWord ++ tailWord_2568140) baseStart_2568140 baseEnd_2568140 := by
    simpa [prefixWord, tailWord_2568140, baseEnd_2568140] using wordTrace_append hprefix tailTrace_2568140
  have hstable : (prefixWord ++ tailWord_2568140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568140).length < 2 ^ (prefixWord ++ tailWord_2568140).sum := by decide
  have hdescent : baseEnd_2568140 < baseStart_2568140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568198 : List Nat := [6, 2, 1, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_2568198 : Nat := 118140960795 + 2568198 * 2 ^ 59
def prefixEnd_2568198 : Nat := 4983230072969 + 3 ^ 40 * 2568198 * 2
def baseEnd_2568198 : Nat := 1318719989915648147214079

theorem tailTrace_2568198 : CollatzResearch.WordTrace tailWord_2568198 prefixEnd_2568198 1318719989915648147214079 := by
  unfold tailWord_2568198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2927183635933272941991289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 62446584233243156095814165 2927183635933272941991289)
  ·
    refine ⟨2195387726949954706493467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2927183635933272941991289 2195387726949954706493467)
    ·
      refine ⟨3293081590424932059740201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2195387726949954706493467 3293081590424932059740201)
      ·
        refine ⟨2469811192818699044805151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3293081590424932059740201 2469811192818699044805151)
        ·
          refine ⟨3704716789228048567207727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2469811192818699044805151 3704716789228048567207727)
          ·
            refine ⟨5557075183842072850811591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3704716789228048567207727 5557075183842072850811591)
            ·
              refine ⟨8335612775763109276217387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5557075183842072850811591 8335612775763109276217387)
              ·
                refine ⟨12503419163644663914326081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8335612775763109276217387 12503419163644663914326081)
                ·
                  refine ⟨9377564372733497935744561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12503419163644663914326081 9377564372733497935744561)
                  ·
                    refine ⟨7033173279550123451808421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9377564372733497935744561 7033173279550123451808421)
                    ·
                      refine ⟨1318719989915648147214079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7033173279550123451808421 1318719989915648147214079)
                      ·
                        rfl

theorem cell23_2568198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_2568198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568198 prefixEnd_2568198 := by exact prefixLift 2568198
  have htrace : WordTrace (prefixWord ++ tailWord_2568198) baseStart_2568198 baseEnd_2568198 := by
    simpa [prefixWord, tailWord_2568198, baseEnd_2568198] using wordTrace_append hprefix tailTrace_2568198
  have hstable : (prefixWord ++ tailWord_2568198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568198).length < 2 ^ (prefixWord ++ tailWord_2568198).sum := by decide
  have hdescent : baseEnd_2568198 < baseStart_2568198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568267 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 4, 3, 2]
def baseStart_2568267 : Nat := 118140960795 + 2568267 * 2 ^ 59
def prefixEnd_2568267 : Nat := 4983230072969 + 3 ^ 40 * 2568267 * 2
def baseEnd_2568267 : Nat := 1318755420080808377251261

theorem tailTrace_2568267 : CollatzResearch.WordTrace tailWord_2568267 prefixEnd_2568267 1318755420080808377251261 := by
  unfold tailWord_2568267
  simp only [CollatzResearch.WordTrace]
  refine ⟨93672392986614758927983055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62448261991076505951988703 93672392986614758927983055)
  ·
    refine ⟨140508589479922138391974583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93672392986614758927983055 140508589479922138391974583)
    ·
      refine ⟨210762884219883207587961875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140508589479922138391974583 210762884219883207587961875)
      ·
        refine ⟨316144326329824811381942813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210762884219883207587961875 316144326329824811381942813)
        ·
          refine ⟨118554122373684304268228555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 316144326329824811381942813 118554122373684304268228555)
          ·
            refine ⟨177831183560526456402342833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118554122373684304268228555 177831183560526456402342833)
            ·
              refine ⟨133373387670394842301757125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177831183560526456402342833 133373387670394842301757125)
              ·
                refine ⟨25007510188199032931579461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 133373387670394842301757125 25007510188199032931579461)
                ·
                  refine ⟨4688908160287318674671149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25007510188199032931579461 4688908160287318674671149)
                  ·
                    refine ⟨1758340560107744503001681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4688908160287318674671149 1758340560107744503001681)
                    ·
                      refine ⟨1318755420080808377251261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1758340560107744503001681 1318755420080808377251261)
                      ·
                        rfl

theorem cell23_2568267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 3, 2].length) (baseStart_2568267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568267 prefixEnd_2568267 := by exact prefixLift 2568267
  have htrace : WordTrace (prefixWord ++ tailWord_2568267) baseStart_2568267 baseEnd_2568267 := by
    simpa [prefixWord, tailWord_2568267, baseEnd_2568267] using wordTrace_append hprefix tailTrace_2568267
  have hstable : (prefixWord ++ tailWord_2568267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568267).length < 2 ^ (prefixWord ++ tailWord_2568267).sum := by decide
  have hdescent : baseEnd_2568267 < baseStart_2568267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568277 : List Nat := [1, 3, 2, 2, 1, 3, 1, 4, 1, 5]
def baseStart_2568277 : Nat := 118140960795 + 2568277 * 2 ^ 59
def prefixEnd_2568277 : Nat := 4983230072969 + 3 ^ 40 * 2568277 * 2
def baseEnd_2568277 : Nat := 439586851629117779375405

theorem tailTrace_2568277 : CollatzResearch.WordTrace tailWord_2568277 prefixEnd_2568277 439586851629117779375405 := by
  unfold tailWord_2568277
  simp only [CollatzResearch.WordTrace]
  refine ⟨93672757716578530635847085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62448505144385687090564723 93672757716578530635847085)
  ·
    refine ⟨35127284143716948988442657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93672757716578530635847085 35127284143716948988442657)
    ·
      refine ⟨26345463107787711741331993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35127284143716948988442657 26345463107787711741331993)
      ·
        refine ⟨19759097330840783805998995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26345463107787711741331993 19759097330840783805998995)
        ·
          refine ⟨29638645996261175708998493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19759097330840783805998995 29638645996261175708998493)
          ·
            refine ⟨11114492248597940890874435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29638645996261175708998493 11114492248597940890874435)
            ·
              refine ⟨16671738372896911336311653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11114492248597940890874435 16671738372896911336311653)
              ·
                refine ⟨3125950944918170875558435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16671738372896911336311653 3125950944918170875558435)
                ·
                  refine ⟨4688926417377256313337653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3125950944918170875558435 4688926417377256313337653)
                  ·
                    refine ⟨439586851629117779375405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4688926417377256313337653 439586851629117779375405)
                    ·
                      rfl

theorem cell23_2568277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_2568277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568277 prefixEnd_2568277 := by exact prefixLift 2568277
  have htrace : WordTrace (prefixWord ++ tailWord_2568277) baseStart_2568277 baseEnd_2568277 := by
    simpa [prefixWord, tailWord_2568277, baseEnd_2568277] using wordTrace_append hprefix tailTrace_2568277
  have hstable : (prefixWord ++ tailWord_2568277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568277).length < 2 ^ (prefixWord ++ tailWord_2568277).sum := by decide
  have hdescent : baseEnd_2568277 < baseStart_2568277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568284 : List Nat := [2, 2, 4, 1, 1, 2, 2, 1, 1, 5, 2]
def baseStart_2568284 : Nat := 118140960795 + 2568284 * 2 ^ 59
def prefixEnd_2568284 : Nat := 4983230072969 + 3 ^ 40 * 2568284 * 2
def baseEnd_2568284 : Nat := 1318764149251934810738683

theorem tailTrace_2568284 : CollatzResearch.WordTrace tailWord_2568284 prefixEnd_2568284 1318764149251934810738683 := by
  unfold tailWord_2568284
  simp only [CollatzResearch.WordTrace]
  refine ⟨46836506513776585415675953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62448675351702113887567937 46836506513776585415675953)
  ·
    refine ⟨35127379885332439061756965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46836506513776585415675953 35127379885332439061756965)
    ·
      refine ⟨6586383728499832324079431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35127379885332439061756965 6586383728499832324079431)
      ·
        refine ⟨9879575592749748486119147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6586383728499832324079431 9879575592749748486119147)
        ·
          refine ⟨14819363389124622729178721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9879575592749748486119147 14819363389124622729178721)
          ·
            refine ⟨11114522541843467046884041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14819363389124622729178721 11114522541843467046884041)
            ·
              refine ⟨8335891906382600285163031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11114522541843467046884041 8335891906382600285163031)
              ·
                refine ⟨12503837859573900427744547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8335891906382600285163031 12503837859573900427744547)
                ·
                  refine ⟨18755756789360850641616821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12503837859573900427744547 18755756789360850641616821)
                  ·
                    refine ⟨1758352199002579747651577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18755756789360850641616821 1758352199002579747651577)
                    ·
                      refine ⟨1318764149251934810738683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1758352199002579747651577 1318764149251934810738683)
                      ·
                        rfl

theorem cell23_2568284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_2568284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568284 prefixEnd_2568284 := by exact prefixLift 2568284
  have htrace : WordTrace (prefixWord ++ tailWord_2568284) baseStart_2568284 baseEnd_2568284 := by
    simpa [prefixWord, tailWord_2568284, baseEnd_2568284] using wordTrace_append hprefix tailTrace_2568284
  have hstable : (prefixWord ++ tailWord_2568284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568284).length < 2 ^ (prefixWord ++ tailWord_2568284).sum := by decide
  have hdescent : baseEnd_2568284 < baseStart_2568284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568291 : List Nat := [1, 1, 1, 5, 1, 1, 5, 3, 1, 1, 3]
def baseStart_2568291 : Nat := 118140960795 + 2568291 * 2 ^ 59
def prefixEnd_2568291 : Nat := 4983230072969 + 3 ^ 40 * 2568291 * 2
def baseEnd_2568291 : Nat := 1318767743616516283351151

theorem tailTrace_2568291 : CollatzResearch.WordTrace tailWord_2568291 prefixEnd_2568291 1318767743616516283351151 := by
  unfold tailWord_2568291
  simp only [CollatzResearch.WordTrace]
  refine ⟨93673268338527811026856727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62448845559018540684571151 93673268338527811026856727)
  ·
    refine ⟨140509902507791716540285091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93673268338527811026856727 140509902507791716540285091)
    ·
      refine ⟨210764853761687574810427637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140509902507791716540285091 210764853761687574810427637)
      ·
        refine ⟨19759205040158210138477591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 210764853761687574810427637 19759205040158210138477591)
        ·
          refine ⟨29638807560237315207716387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19759205040158210138477591 29638807560237315207716387)
          ·
            refine ⟨44458211340355972811574581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29638807560237315207716387 44458211340355972811574581)
            ·
              refine ⟨4167957313158372451085117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44458211340355972811574581 4167957313158372451085117)
              ·
                refine ⟨1562983992434389669156919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4167957313158372451085117 1562983992434389669156919)
                ·
                  refine ⟨2344475988651584503735379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1562983992434389669156919 2344475988651584503735379)
                  ·
                    refine ⟨3516713982977376755603069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2344475988651584503735379 3516713982977376755603069)
                    ·
                      refine ⟨1318767743616516283351151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3516713982977376755603069 1318767743616516283351151)
                      ·
                        rfl

theorem cell23_2568291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_2568291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568291 prefixEnd_2568291 := by exact prefixLift 2568291
  have htrace : WordTrace (prefixWord ++ tailWord_2568291) baseStart_2568291 baseEnd_2568291 := by
    simpa [prefixWord, tailWord_2568291, baseEnd_2568291] using wordTrace_append hprefix tailTrace_2568291
  have hstable : (prefixWord ++ tailWord_2568291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568291).length < 2 ^ (prefixWord ++ tailWord_2568291).sum := by decide
  have hdescent : baseEnd_2568291 < baseStart_2568291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568297 : List Nat := [1, 2, 1, 1, 1, 5, 1, 5, 1, 1, 4]
def baseStart_2568297 : Nat := 118140960795 + 2568297 * 2 ^ 59
def prefixEnd_2568297 : Nat := 4983230072969 + 3 ^ 40 * 2568297 * 2
def baseEnd_2568297 : Nat := 1318770824500443259876123

theorem tailTrace_2568297 : CollatzResearch.WordTrace tailWord_2568297 prefixEnd_2568297 1318770824500443259876123 := by
  unfold tailWord_2568297
  simp only [CollatzResearch.WordTrace]
  refine ⟨93673487176506074051575145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62448991451004049367716763 93673487176506074051575145)
  ·
    refine ⟨70255115382379555538681359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93673487176506074051575145 70255115382379555538681359)
    ·
      refine ⟨105382673073569333308022039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70255115382379555538681359 105382673073569333308022039)
      ·
        refine ⟨158074009610353999962033059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105382673073569333308022039 158074009610353999962033059)
        ·
          refine ⟨237111014415530999943049589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158074009610353999962033059 237111014415530999943049589)
          ·
            refine ⟨22229157601456031244660899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 237111014415530999943049589 22229157601456031244660899)
            ·
              refine ⟨33343736402184046866991349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22229157601456031244660899 33343736402184046866991349)
              ·
                refine ⟨3125975287704754393780439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33343736402184046866991349 3125975287704754393780439)
                ·
                  refine ⟨4688962931557131590670659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3125975287704754393780439 4688962931557131590670659)
                  ·
                    refine ⟨7033444397335697386005989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4688962931557131590670659 7033444397335697386005989)
                    ·
                      refine ⟨1318770824500443259876123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7033444397335697386005989 1318770824500443259876123)
                      ·
                        rfl

theorem cell23_2568297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 1, 4].length) (baseStart_2568297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568297 prefixEnd_2568297 := by exact prefixLift 2568297
  have htrace : WordTrace (prefixWord ++ tailWord_2568297) baseStart_2568297 baseEnd_2568297 := by
    simpa [prefixWord, tailWord_2568297, baseEnd_2568297] using wordTrace_append hprefix tailTrace_2568297
  have hstable : (prefixWord ++ tailWord_2568297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568297).length < 2 ^ (prefixWord ++ tailWord_2568297).sum := by decide
  have hdescent : baseEnd_2568297 < baseStart_2568297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568317 : List Nat := [1, 4, 1, 1, 3, 2, 2, 2, 1, 1, 5]
def baseStart_2568317 : Nat := 118140960795 + 2568317 * 2 ^ 59
def prefixEnd_2568317 : Nat := 4983230072969 + 3 ^ 40 * 2568317 * 2
def baseEnd_2568317 : Nat := 1318781094113533181626031

theorem tailTrace_2568317 : CollatzResearch.WordTrace tailWord_2568317 prefixEnd_2568317 1318781094113533181626031 := by
  unfold tailWord_2568317
  simp only [CollatzResearch.WordTrace]
  refine ⟨93674216636433617467303205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62449477757622411644868803 93674216636433617467303205)
  ·
    refine ⟨17563915619331303275119351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93674216636433617467303205 17563915619331303275119351)
    ·
      refine ⟨26345873428996954912679027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17563915619331303275119351 26345873428996954912679027)
      ·
        refine ⟨39518810143495432369018541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26345873428996954912679027 39518810143495432369018541)
        ·
          refine ⟨14819553803810787138381953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39518810143495432369018541 14819553803810787138381953)
          ·
            refine ⟨11114665352858090353786465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14819553803810787138381953 11114665352858090353786465)
            ·
              refine ⟨8335999014643567765339849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11114665352858090353786465 8335999014643567765339849)
              ·
                refine ⟨6251999260982675824004887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8335999014643567765339849 6251999260982675824004887)
                ·
                  refine ⟨9377998891474013736007331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6251999260982675824004887 9377998891474013736007331)
                  ·
                    refine ⟨14066998337211020604010997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9377998891474013736007331 14066998337211020604010997)
                    ·
                      refine ⟨1318781094113533181626031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14066998337211020604010997 1318781094113533181626031)
                      ·
                        rfl

theorem cell23_2568317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_2568317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568317 prefixEnd_2568317 := by exact prefixLift 2568317
  have htrace : WordTrace (prefixWord ++ tailWord_2568317) baseStart_2568317 baseEnd_2568317 := by
    simpa [prefixWord, tailWord_2568317, baseEnd_2568317] using wordTrace_append hprefix tailTrace_2568317
  have hstable : (prefixWord ++ tailWord_2568317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568317).length < 2 ^ (prefixWord ++ tailWord_2568317).sum := by decide
  have hdescent : baseEnd_2568317 < baseStart_2568317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568324 : List Nat := [2, 3, 2, 1, 2, 1, 3, 3, 2, 4]
def baseStart_2568324 : Nat := 118140960795 + 2568324 * 2 ^ 59
def prefixEnd_2568324 : Nat := 4983230072969 + 3 ^ 40 * 2568324 * 2
def baseEnd_2568324 : Nat := 439594896159371551412833

theorem tailTrace_2568324 : CollatzResearch.WordTrace tailWord_2568324 prefixEnd_2568324 439594896159371551412833 := by
  unfold tailWord_2568324
  simp only [CollatzResearch.WordTrace]
  refine ⟨46837235973704128831404013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62449647964938838441872017 46837235973704128831404013)
  ·
    refine ⟨17563963490139048311776505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46837235973704128831404013 17563963490139048311776505)
    ·
      refine ⟨13172972617604286233832379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17563963490139048311776505 13172972617604286233832379)
      ·
        refine ⟨19759458926406429350748569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13172972617604286233832379 19759458926406429350748569)
        ·
          refine ⟨14819594194804822013061427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19759458926406429350748569 14819594194804822013061427)
          ·
            refine ⟨22229391292207233019592141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14819594194804822013061427 22229391292207233019592141)
            ·
              refine ⟨8336021734577712382347053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22229391292207233019592141 8336021734577712382347053)
              ·
                refine ⟨3126008150466642143380145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8336021734577712382347053 3126008150466642143380145)
                ·
                  refine ⟨2344506112849981607535109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3126008150466642143380145 2344506112849981607535109)
                  ·
                    refine ⟨439594896159371551412833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2344506112849981607535109 439594896159371551412833)
                    ·
                      rfl

theorem cell23_2568324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_2568324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568324 prefixEnd_2568324 := by exact prefixLift 2568324
  have htrace : WordTrace (prefixWord ++ tailWord_2568324) baseStart_2568324 baseEnd_2568324 := by
    simpa [prefixWord, tailWord_2568324, baseEnd_2568324] using wordTrace_append hprefix tailTrace_2568324
  have hstable : (prefixWord ++ tailWord_2568324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568324).length < 2 ^ (prefixWord ++ tailWord_2568324).sum := by decide
  have hdescent : baseEnd_2568324 < baseStart_2568324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568344 : List Nat := [2, 1, 2, 4, 3, 1, 1, 2, 1, 2, 4]
def baseStart_2568344 : Nat := 118140960795 + 2568344 * 2 ^ 59
def prefixEnd_2568344 : Nat := 4983230072969 + 3 ^ 40 * 2568344 * 2
def baseEnd_2568344 : Nat := 1318794958091204575988407

theorem tailTrace_2568344 : CollatzResearch.WordTrace tailWord_2568344 prefixEnd_2568344 1318794958091204575988407 := by
  unfold tailWord_2568344
  simp only [CollatzResearch.WordTrace]
  refine ⟨46837600703667900539268043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62450134271557200719024057 46837600703667900539268043)
  ·
    refine ⟨70256401055501850808902065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46837600703667900539268043 70256401055501850808902065)
    ·
      refine ⟨52692300791626388106676549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70256401055501850808902065 52692300791626388106676549)
      ·
        refine ⟨9879806398429947770001853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52692300791626388106676549 9879806398429947770001853)
        ·
          refine ⟨3704927399411230413750695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9879806398429947770001853 3704927399411230413750695)
          ·
            refine ⟨5557391099116845620626043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3704927399411230413750695 5557391099116845620626043)
            ·
              refine ⟨8336086648675268430939065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5557391099116845620626043 8336086648675268430939065)
              ·
                refine ⟨6252064986506451323204299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8336086648675268430939065 6252064986506451323204299)
                ·
                  refine ⟨9378097479759676984806449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6252064986506451323204299 9378097479759676984806449)
                  ·
                    refine ⟨7033573109819757738604837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9378097479759676984806449 7033573109819757738604837)
                    ·
                      refine ⟨1318794958091204575988407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7033573109819757738604837 1318794958091204575988407)
                      ·
                        rfl

theorem cell23_2568344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_2568344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568344 prefixEnd_2568344 := by exact prefixLift 2568344
  have htrace : WordTrace (prefixWord ++ tailWord_2568344) baseStart_2568344 baseEnd_2568344 := by
    simpa [prefixWord, tailWord_2568344, baseEnd_2568344] using wordTrace_append hprefix tailTrace_2568344
  have hstable : (prefixWord ++ tailWord_2568344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568344).length < 2 ^ (prefixWord ++ tailWord_2568344).sum := by decide
  have hdescent : baseEnd_2568344 < baseStart_2568344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568348 : List Nat := [2, 2, 3, 2, 1, 1, 2, 5, 1, 2, 2]
def baseStart_2568348 : Nat := 118140960795 + 2568348 * 2 ^ 59
def prefixEnd_2568348 : Nat := 4983230072969 + 3 ^ 40 * 2568348 * 2
def baseEnd_2568348 : Nat := 1318797012013822560338389

theorem tailTrace_2568348 : CollatzResearch.WordTrace tailWord_2568348 prefixEnd_2568348 1318797012013822560338389 := by
  unfold tailWord_2568348
  simp only [CollatzResearch.WordTrace]
  refine ⟨46837673649660654880840849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62450231532880873174454465 46837673649660654880840849)
  ·
    refine ⟨35128255237245491160630637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46837673649660654880840849 35128255237245491160630637)
    ·
      refine ⟨13173095713967059185236489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35128255237245491160630637 13173095713967059185236489)
      ·
        refine ⟨9879821785475294388927367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13173095713967059185236489 9879821785475294388927367)
        ·
          refine ⟨14819732678212941583391051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9879821785475294388927367 14819732678212941583391051)
          ·
            refine ⟨22229599017319412375086577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14819732678212941583391051 22229599017319412375086577)
            ·
              refine ⟨16672199262989559281314933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22229599017319412375086577 16672199262989559281314933)
              ·
                refine ⟨1563018680905271182623275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16672199262989559281314933 1563018680905271182623275)
                ·
                  refine ⟨2344528021357906773934913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1563018680905271182623275 2344528021357906773934913)
                  ·
                    refine ⟨1758396016018430080451185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2344528021357906773934913 1758396016018430080451185)
                    ·
                      refine ⟨1318797012013822560338389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1758396016018430080451185 1318797012013822560338389)
                      ·
                        rfl

theorem cell23_2568348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_2568348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568348 prefixEnd_2568348 := by exact prefixLift 2568348
  have htrace : WordTrace (prefixWord ++ tailWord_2568348) baseStart_2568348 baseEnd_2568348 := by
    simpa [prefixWord, tailWord_2568348, baseEnd_2568348] using wordTrace_append hprefix tailTrace_2568348
  have hstable : (prefixWord ++ tailWord_2568348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568348).length < 2 ^ (prefixWord ++ tailWord_2568348).sum := by decide
  have hdescent : baseEnd_2568348 < baseStart_2568348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568365 : List Nat := [1, 5, 2, 1, 2, 2, 1, 4, 1, 2, 2]
def baseStart_2568365 : Nat := 118140960795 + 2568365 * 2 ^ 59
def prefixEnd_2568365 : Nat := 4983230072969 + 3 ^ 40 * 2568365 * 2
def baseEnd_2568365 : Nat := 1318805741184948993825811

theorem tailTrace_2568365 : CollatzResearch.WordTrace tailWord_2568365 prefixEnd_2568365 1318805741184948993825811 := by
  unfold tailWord_2568365
  simp only [CollatzResearch.WordTrace]
  refine ⟨93675967340259721665050549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62450644893506481110033699 93675967340259721665050549)
  ·
    refine ⟨8782121938149348906098489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93675967340259721665050549 8782121938149348906098489)
    ·
      refine ⟨6586591453612011679573867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8782121938149348906098489 6586591453612011679573867)
      ·
        refine ⟨9879887180418017519360801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6586591453612011679573867 9879887180418017519360801)
        ·
          refine ⟨7409915385313513139520601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9879887180418017519360801 7409915385313513139520601)
          ·
            refine ⟨5557436538985134854640451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7409915385313513139520601 5557436538985134854640451)
            ·
              refine ⟨8336154808477702281960677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5557436538985134854640451 8336154808477702281960677)
              ·
                refine ⟨1563029026589569177867627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8336154808477702281960677 1563029026589569177867627)
                ·
                  refine ⟨2344543539884353766801441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1563029026589569177867627 2344543539884353766801441)
                  ·
                    refine ⟨1758407654913265325101081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2344543539884353766801441 1758407654913265325101081)
                    ·
                      refine ⟨1318805741184948993825811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1758407654913265325101081 1318805741184948993825811)
                      ·
                        rfl

theorem cell23_2568365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_2568365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568365 prefixEnd_2568365 := by exact prefixLift 2568365
  have htrace : WordTrace (prefixWord ++ tailWord_2568365) baseStart_2568365 baseEnd_2568365 := by
    simpa [prefixWord, tailWord_2568365, baseEnd_2568365] using wordTrace_append hprefix tailTrace_2568365
  have hstable : (prefixWord ++ tailWord_2568365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568365).length < 2 ^ (prefixWord ++ tailWord_2568365).sum := by decide
  have hdescent : baseEnd_2568365 < baseStart_2568365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568408 : List Nat := [2, 1, 2, 2, 4, 1, 4, 1, 1, 3, 2]
def baseStart_2568408 : Nat := 118140960795 + 2568408 * 2 ^ 59
def prefixEnd_2568408 : Nat := 4983230072969 + 3 ^ 40 * 2568408 * 2
def baseEnd_2568408 : Nat := 1318827820853092325588113

theorem tailTrace_2568408 : CollatzResearch.WordTrace tailWord_2568408 prefixEnd_2568408 1318827820853092325588113 := by
  unfold tailWord_2568408
  simp only [CollatzResearch.WordTrace]
  refine ⟨46838767839551970004432939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62451690452735960005910585 46838767839551970004432939)
  ·
    refine ⟨70258151759327955006649409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46838767839551970004432939 70258151759327955006649409)
    ·
      refine ⟨52693613819495966254987057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70258151759327955006649409 52693613819495966254987057)
      ·
        refine ⟨39520210364621974691240293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52693613819495966254987057 39520210364621974691240293)
        ·
          refine ⟨7410039443366620254607555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39520210364621974691240293 7410039443366620254607555)
          ·
            refine ⟨11115059165049930381911333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7410039443366620254607555 11115059165049930381911333)
            ·
              refine ⟨2084073593446861946608375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11115059165049930381911333 2084073593446861946608375)
              ·
                refine ⟨3126110390170292919912563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2084073593446861946608375 3126110390170292919912563)
                ·
                  refine ⟨4689165585255439379868845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3126110390170292919912563 4689165585255439379868845)
                  ·
                    refine ⟨1758437094470789767450817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4689165585255439379868845 1758437094470789767450817)
                    ·
                      refine ⟨1318827820853092325588113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1758437094470789767450817 1318827820853092325588113)
                      ·
                        rfl

theorem cell23_2568408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 1, 3, 2].length) (baseStart_2568408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568408 prefixEnd_2568408 := by exact prefixLift 2568408
  have htrace : WordTrace (prefixWord ++ tailWord_2568408) baseStart_2568408 baseEnd_2568408 := by
    simpa [prefixWord, tailWord_2568408, baseEnd_2568408] using wordTrace_append hprefix tailTrace_2568408
  have hstable : (prefixWord ++ tailWord_2568408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568408).length < 2 ^ (prefixWord ++ tailWord_2568408).sum := by decide
  have hdescent : baseEnd_2568408 < baseStart_2568408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568417 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 4, 2, 4]
def baseStart_2568417 : Nat := 118140960795 + 2568417 * 2 ^ 59
def prefixEnd_2568417 : Nat := 4983230072969 + 3 ^ 40 * 2568417 * 2
def baseEnd_2568417 : Nat := 1318832442178982790375571

theorem tailTrace_2568417 : CollatzResearch.WordTrace tailWord_2568417 prefixEnd_2568417 1318832442178982790375571 := by
  unfold tailWord_2568417
  simp only [CollatzResearch.WordTrace]
  refine ⟨93677863936071334545943505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62451909290714223030629003 93677863936071334545943505)
  ·
    refine ⟨70258397952053500909457629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93677863936071334545943505 70258397952053500909457629)
    ·
      refine ⟨26346899232020062841046611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70258397952053500909457629 26346899232020062841046611)
      ·
        refine ⟨39520348848030094261569917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26346899232020062841046611 39520348848030094261569917)
        ·
          refine ⟨14820130818011285348088719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39520348848030094261569917 14820130818011285348088719)
          ·
            refine ⟨22230196227016928022133079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14820130818011285348088719 22230196227016928022133079)
            ·
              refine ⟨33345294340525392033199619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22230196227016928022133079 33345294340525392033199619)
              ·
                refine ⟨50017941510788088049799429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33345294340525392033199619 50017941510788088049799429)
                ·
                  refine ⟨9378364033272766509337393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50017941510788088049799429 9378364033272766509337393)
                  ·
                    refine ⟨7033773024954574882003045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9378364033272766509337393 7033773024954574882003045)
                    ·
                      refine ⟨1318832442178982790375571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7033773024954574882003045 1318832442178982790375571)
                      ·
                        rfl

theorem cell23_2568417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_2568417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568417 prefixEnd_2568417 := by exact prefixLift 2568417
  have htrace : WordTrace (prefixWord ++ tailWord_2568417) baseStart_2568417 baseEnd_2568417 := by
    simpa [prefixWord, tailWord_2568417, baseEnd_2568417] using wordTrace_append hprefix tailTrace_2568417
  have hstable : (prefixWord ++ tailWord_2568417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568417).length < 2 ^ (prefixWord ++ tailWord_2568417).sum := by decide
  have hdescent : baseEnd_2568417 < baseStart_2568417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568427 : List Nat := [1, 1, 1, 1, 2, 5, 4, 1, 7]
def baseStart_2568427 : Nat := 118140960795 + 2568427 * 2 ^ 59
def prefixEnd_2568427 : Nat := 4983230072969 + 3 ^ 40 * 2568427 * 2
def baseEnd_2568427 : Nat := 146537508553947527916725

theorem tailTrace_2568427 : CollatzResearch.WordTrace tailWord_2568427 prefixEnd_2568427 146537508553947527916725 := by
  unfold tailWord_2568427
  simp only [CollatzResearch.WordTrace]
  refine ⟨93678228666035106253807535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62452152444023404169205023 93678228666035106253807535)
  ·
    refine ⟨140517342999052659380711303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93678228666035106253807535 140517342999052659380711303)
    ·
      refine ⟨210776014498578989071066955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140517342999052659380711303 210776014498578989071066955)
      ·
        refine ⟨316164021747868483606600433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210776014498578989071066955 316164021747868483606600433)
        ·
          refine ⟨237123016310901362704950325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 316164021747868483606600433 237123016310901362704950325)
          ·
            refine ⟨22230282779147002753589093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 237123016310901362704950325 22230282779147002753589093)
            ·
              refine ⟨4168178021090063016297955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22230282779147002753589093 4168178021090063016297955)
              ·
                refine ⟨6252267031635094524446933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4168178021090063016297955 6252267031635094524446933)
                ·
                  refine ⟨146537508553947527916725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6252267031635094524446933 146537508553947527916725)
                  ·
                    rfl

theorem cell23_2568427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 7].length) (baseStart_2568427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568427 prefixEnd_2568427 := by exact prefixLift 2568427
  have htrace : WordTrace (prefixWord ++ tailWord_2568427) baseStart_2568427 baseEnd_2568427 := by
    simpa [prefixWord, tailWord_2568427, baseEnd_2568427] using wordTrace_append hprefix tailTrace_2568427
  have hstable : (prefixWord ++ tailWord_2568427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568427).length < 2 ^ (prefixWord ++ tailWord_2568427).sum := by decide
  have hdescent : baseEnd_2568427 < baseStart_2568427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568434 : List Nat := [3, 2, 1, 3, 2, 1, 2, 1, 2, 2, 4]
def baseStart_2568434 : Nat := 118140960795 + 2568434 * 2 ^ 59
def prefixEnd_2568434 : Nat := 4983230072969 + 3 ^ 40 * 2568434 * 2
def baseEnd_2568434 : Nat := 1318841171350109223862993

theorem tailTrace_2568434 : CollatzResearch.WordTrace tailWord_2568434 prefixEnd_2568434 1318841171350109223862993 := by
  unfold tailWord_2568434
  simp only [CollatzResearch.WordTrace]
  refine ⟨23419620994252436612328089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62452322651339830966208237 23419620994252436612328089)
  ·
    refine ⟨17564715745689327459246067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23419620994252436612328089 17564715745689327459246067)
    ·
      refine ⟨26347073618533991188869101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17564715745689327459246067 26347073618533991188869101)
      ·
        refine ⟨9880152606950246695825913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26347073618533991188869101 9880152606950246695825913)
        ·
          refine ⟨7410114455212685021869435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9880152606950246695825913 7410114455212685021869435)
          ·
            refine ⟨11115171682819027532804153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7410114455212685021869435 11115171682819027532804153)
            ·
              refine ⟨8336378762114270649603115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11115171682819027532804153 8336378762114270649603115)
              ·
                refine ⟨12504568143171405974404673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8336378762114270649603115 12504568143171405974404673)
                ·
                  refine ⟨9378426107378554480803505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12504568143171405974404673 9378426107378554480803505)
                  ·
                    refine ⟨7033819580533915860602629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9378426107378554480803505 7033819580533915860602629)
                    ·
                      refine ⟨1318841171350109223862993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7033819580533915860602629 1318841171350109223862993)
                      ·
                        rfl

theorem cell23_2568434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_2568434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568434 prefixEnd_2568434 := by exact prefixLift 2568434
  have htrace : WordTrace (prefixWord ++ tailWord_2568434) baseStart_2568434 baseEnd_2568434 := by
    simpa [prefixWord, tailWord_2568434, baseEnd_2568434] using wordTrace_append hprefix tailTrace_2568434
  have hstable : (prefixWord ++ tailWord_2568434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568434).length < 2 ^ (prefixWord ++ tailWord_2568434).sum := by decide
  have hdescent : baseEnd_2568434 < baseStart_2568434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568438 : List Nat := [5, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2]
def baseStart_2568438 : Nat := 118140960795 + 2568438 * 2 ^ 59
def prefixEnd_2568438 : Nat := 4983230072969 + 3 ^ 40 * 2568438 * 2
def baseEnd_2568438 : Nat := 1318843225272727208212975

theorem tailTrace_2568438 : CollatzResearch.WordTrace tailWord_2568438 prefixEnd_2568438 1318843225272727208212975 := by
  unfold tailWord_2568438
  simp only [CollatzResearch.WordTrace]
  refine ⟨5854914366812203445778623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62452419912663503421638645 5854914366812203445778623)
  ·
    refine ⟨8782371550218305168667935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5854914366812203445778623 8782371550218305168667935)
    ·
      refine ⟨13173557325327457753001903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8782371550218305168667935 13173557325327457753001903)
      ·
        refine ⟨19760335987991186629502855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13173557325327457753001903 19760335987991186629502855)
        ·
          refine ⟨29640503981986779944254283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19760335987991186629502855 29640503981986779944254283)
          ·
            refine ⟨44460755972980169916381425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29640503981986779944254283 44460755972980169916381425)
            ·
              refine ⟨33345566979735127437286069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44460755972980169916381425 33345566979735127437286069)
              ·
                refine ⟨3126146904350168197245569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33345566979735127437286069 3126146904350168197245569)
                ·
                  refine ⟨2344610178262626147934177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3126146904350168197245569 2344610178262626147934177)
                  ·
                    refine ⟨1758457633696969610950633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2344610178262626147934177 1758457633696969610950633)
                    ·
                      refine ⟨1318843225272727208212975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1758457633696969610950633 1318843225272727208212975)
                      ·
                        rfl

theorem cell23_2568438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_2568438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568438 prefixEnd_2568438 := by exact prefixLift 2568438
  have htrace : WordTrace (prefixWord ++ tailWord_2568438) baseStart_2568438 baseEnd_2568438 := by
    simpa [prefixWord, tailWord_2568438, baseEnd_2568438] using wordTrace_append hprefix tailTrace_2568438
  have hstable : (prefixWord ++ tailWord_2568438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568438).length < 2 ^ (prefixWord ++ tailWord_2568438).sum := by decide
  have hdescent : baseEnd_2568438 < baseStart_2568438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568457 : List Nat := [1, 2, 1, 1, 3, 4, 2, 1, 1, 7]
def baseStart_2568457 : Nat := 118140960795 + 2568457 * 2 ^ 59
def prefixEnd_2568457 : Nat := 4983230072969 + 3 ^ 40 * 2568457 * 2
def baseEnd_2568457 : Nat := 439617660468387544625129

theorem tailTrace_2568457 : CollatzResearch.WordTrace tailWord_2568457 prefixEnd_2568457 439617660468387544625129 := by
  unfold tailWord_2568457
  simp only [CollatzResearch.WordTrace]
  refine ⟨93679322855926421377399625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62452881903950947584933083 93679322855926421377399625)
  ·
    refine ⟨70259492141944816033049719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93679322855926421377399625 70259492141944816033049719)
    ·
      refine ⟨105389238212917224049574579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70259492141944816033049719 105389238212917224049574579)
      ·
        refine ⟨158083857319375836074361869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105389238212917224049574579 158083857319375836074361869)
        ·
          refine ⟨59281446494765938527885701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158083857319375836074361869 59281446494765938527885701)
          ·
            refine ⟨11115271217768613473978569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59281446494765938527885701 11115271217768613473978569)
            ·
              refine ⟨8336453413326460105483927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11115271217768613473978569 8336453413326460105483927)
              ·
                refine ⟨12504680119989690158225891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8336453413326460105483927 12504680119989690158225891)
                ·
                  refine ⟨18757020179984535237338837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12504680119989690158225891 18757020179984535237338837)
                  ·
                    refine ⟨439617660468387544625129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18757020179984535237338837 439617660468387544625129)
                    ·
                      rfl

theorem cell23_2568457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 7].length) (baseStart_2568457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568457 prefixEnd_2568457 := by exact prefixLift 2568457
  have htrace : WordTrace (prefixWord ++ tailWord_2568457) baseStart_2568457 baseEnd_2568457 := by
    simpa [prefixWord, tailWord_2568457, baseEnd_2568457] using wordTrace_append hprefix tailTrace_2568457
  have hstable : (prefixWord ++ tailWord_2568457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568457).length < 2 ^ (prefixWord ++ tailWord_2568457).sum := by decide
  have hdescent : baseEnd_2568457 < baseStart_2568457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568478 : List Nat := [4, 3, 2, 1, 1, 3, 1, 1, 7]
def baseStart_2568478 : Nat := 118140960795 + 2568478 * 2 ^ 59
def prefixEnd_2568478 : Nat := 4983230072969 + 3 ^ 40 * 2568478 * 2
def baseEnd_2568478 : Nat := 146540418277656339079199

theorem tailTrace_2568478 : CollatzResearch.WordTrace tailWord_2568478 prefixEnd_2568478 146540418277656339079199 := by
  unfold tailWord_2568478
  simp only [CollatzResearch.WordTrace]
  refine ⟨11710011098606292745489261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62453392525900227975942725 11710011098606292745489261)
  ·
    refine ⟨4391254161977359779558473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11710011098606292745489261 4391254161977359779558473)
    ·
      refine ⟨3293440621483019834668855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4391254161977359779558473 3293440621483019834668855)
      ·
        refine ⟨4940160932224529752003283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3293440621483019834668855 4940160932224529752003283)
        ·
          refine ⟨7410241398336794628004925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4940160932224529752003283 7410241398336794628004925)
          ·
            refine ⟨2778840524376297985501847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7410241398336794628004925 2778840524376297985501847)
            ·
              refine ⟨4168260786564446978252771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2778840524376297985501847 4168260786564446978252771)
              ·
                refine ⟨6252391179846670467379157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4168260786564446978252771 6252391179846670467379157)
                ·
                  refine ⟨146540418277656339079199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6252391179846670467379157 146540418277656339079199)
                  ·
                    rfl

theorem cell23_2568478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_2568478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568478 prefixEnd_2568478 := by exact prefixLift 2568478
  have htrace : WordTrace (prefixWord ++ tailWord_2568478) baseStart_2568478 baseEnd_2568478 := by
    simpa [prefixWord, tailWord_2568478, baseEnd_2568478] using wordTrace_append hprefix tailTrace_2568478
  have hstable : (prefixWord ++ tailWord_2568478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568478).length < 2 ^ (prefixWord ++ tailWord_2568478).sum := by decide
  have hdescent : baseEnd_2568478 < baseStart_2568478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568484 : List Nat := [2, 3, 1, 3, 1, 3, 1, 1, 1, 2, 5]
def baseStart_2568484 : Nat := 118140960795 + 2568484 * 2 ^ 59
def prefixEnd_2568484 : Nat := 4983230072969 + 3 ^ 40 * 2568484 * 2
def baseEnd_2568484 : Nat := 1318866845382834028237763

theorem tailTrace_2568484 : CollatzResearch.WordTrace tailWord_2568484 prefixEnd_2568484 1318866845382834028237763 := by
  unfold tailWord_2568484
  simp only [CollatzResearch.WordTrace]
  refine ⟨46840153813414302494316253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62453538417885736659088337 46840153813414302494316253)
  ·
    refine ⟨17565057680030363435368595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46840153813414302494316253 17565057680030363435368595)
    ·
      refine ⟨26347586520045545153052893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17565057680030363435368595 26347586520045545153052893)
      ·
        refine ⟨9880344945017079432394835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26347586520045545153052893 9880344945017079432394835)
        ·
          refine ⟨14820517417525619148592253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9880344945017079432394835 14820517417525619148592253)
          ·
            refine ⟨5557694031572107180722095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14820517417525619148592253 5557694031572107180722095)
            ·
              refine ⟨8336541047358160771083143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5557694031572107180722095 8336541047358160771083143)
              ·
                refine ⟨12504811571037241156624715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8336541047358160771083143 12504811571037241156624715)
                ·
                  refine ⟨18757217356555861734937073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12504811571037241156624715 18757217356555861734937073)
                  ·
                    refine ⟨14067913017416896301202805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18757217356555861734937073 14067913017416896301202805)
                    ·
                      refine ⟨1318866845382834028237763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14067913017416896301202805 1318866845382834028237763)
                      ·
                        rfl

theorem cell23_2568484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_2568484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568484 prefixEnd_2568484 := by exact prefixLift 2568484
  have htrace : WordTrace (prefixWord ++ tailWord_2568484) baseStart_2568484 baseEnd_2568484 := by
    simpa [prefixWord, tailWord_2568484, baseEnd_2568484] using wordTrace_append hprefix tailTrace_2568484
  have hstable : (prefixWord ++ tailWord_2568484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568484).length < 2 ^ (prefixWord ++ tailWord_2568484).sum := by decide
  have hdescent : baseEnd_2568484 < baseStart_2568484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568504 : List Nat := [2, 1, 2, 1, 3, 1, 2, 4, 3, 4]
def baseStart_2568504 : Nat := 118140960795 + 2568504 * 2 ^ 59
def prefixEnd_2568504 : Nat := 4983230072969 + 3 ^ 40 * 2568504 * 2
def baseEnd_2568504 : Nat := 439625704998641316662557

theorem tailTrace_2568504 : CollatzResearch.WordTrace tailWord_2568504 prefixEnd_2568504 439625704998641316662557 := by
  unfold tailWord_2568504
  simp only [CollatzResearch.WordTrace]
  refine ⟨46840518543378074202180283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62454024724504098936240377 46840518543378074202180283)
  ·
    refine ⟨70260777815067111303270425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46840518543378074202180283 70260777815067111303270425)
    ·
      refine ⟨52695583361300333477452819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70260777815067111303270425 52695583361300333477452819)
      ·
        refine ⟨79043375041950500216179229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52695583361300333477452819 79043375041950500216179229)
        ·
          refine ⟨29641265640731437581067211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79043375041950500216179229 29641265640731437581067211)
          ·
            refine ⟨44461898461097156371600817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29641265640731437581067211 44461898461097156371600817)
            ·
              refine ⟨33346423845822867278700613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44461898461097156371600817 33346423845822867278700613)
              ·
                refine ⟨6252454471091787614756365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33346423845822867278700613 6252454471091787614756365)
                ·
                  refine ⟨2344670426659420355533637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6252454471091787614756365 2344670426659420355533637)
                  ·
                    refine ⟨439625704998641316662557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2344670426659420355533637 439625704998641316662557)
                    ·
                      rfl

theorem cell23_2568504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 3, 4].length) (baseStart_2568504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568504 prefixEnd_2568504 := by exact prefixLift 2568504
  have htrace : WordTrace (prefixWord ++ tailWord_2568504) baseStart_2568504 baseEnd_2568504 := by
    simpa [prefixWord, tailWord_2568504, baseEnd_2568504] using wordTrace_append hprefix tailTrace_2568504
  have hstable : (prefixWord ++ tailWord_2568504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568504).length < 2 ^ (prefixWord ++ tailWord_2568504).sum := by decide
  have hdescent : baseEnd_2568504 < baseStart_2568504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568521 : List Nat := [1, 2, 1, 1, 2, 3, 1, 7, 1, 4]
def baseStart_2568521 : Nat := 118140960795 + 2568521 * 2 ^ 59
def prefixEnd_2568521 : Nat := 4983230072969 + 3 ^ 40 * 2568521 * 2
def baseEnd_2568521 : Nat := 439628614722350127825031

theorem tailTrace_2568521 : CollatzResearch.WordTrace tailWord_2568521 prefixEnd_2568521 439628614722350127825031 := by
  unfold tailWord_2568521
  simp only [CollatzResearch.WordTrace]
  refine ⟨93681657127694560307729417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62454438085129706871819611 93681657127694560307729417)
  ·
    refine ⟨70261242845770920230797063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93681657127694560307729417 70261242845770920230797063)
    ·
      refine ⟨105391864268656380346195595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70261242845770920230797063 105391864268656380346195595)
      ·
        refine ⟨158087796402984570519293393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105391864268656380346195595 158087796402984570519293393)
        ·
          refine ⟨118565847302238427889470045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158087796402984570519293393 118565847302238427889470045)
          ·
            refine ⟨44462192738339410458551267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118565847302238427889470045 44462192738339410458551267)
            ·
              refine ⟨66693289107509115687826901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44462192738339410458551267 66693289107509115687826901)
              ·
                refine ⟨1563123963457244898933443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 66693289107509115687826901 1563123963457244898933443)
                ·
                  refine ⟨2344685945185867348400165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1563123963457244898933443 2344685945185867348400165)
                  ·
                    refine ⟨439628614722350127825031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2344685945185867348400165 439628614722350127825031)
                    ·
                      rfl

theorem cell23_2568521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 7, 1, 4].length) (baseStart_2568521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568521 prefixEnd_2568521 := by exact prefixLift 2568521
  have htrace : WordTrace (prefixWord ++ tailWord_2568521) baseStart_2568521 baseEnd_2568521 := by
    simpa [prefixWord, tailWord_2568521, baseEnd_2568521] using wordTrace_append hprefix tailTrace_2568521
  have hstable : (prefixWord ++ tailWord_2568521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568521).length < 2 ^ (prefixWord ++ tailWord_2568521).sum := by decide
  have hdescent : baseEnd_2568521 < baseStart_2568521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568537 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 1, 2, 6]
def baseStart_2568537 : Nat := 118140960795 + 2568537 * 2 ^ 59
def prefixEnd_2568537 : Nat := 4983230072969 + 3 ^ 40 * 2568537 * 2
def baseEnd_2568537 : Nat := 1318894059857522320875019

theorem tailTrace_2568537 : CollatzResearch.WordTrace tailWord_2568537 prefixEnd_2568537 1318894059857522320875019 := by
  unfold tailWord_2568537
  simp only [CollatzResearch.WordTrace]
  refine ⟨93682240695636595040311865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62454827130424396693541243 93682240695636595040311865)
  ·
    refine ⟨70261680521727446280233899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93682240695636595040311865 70261680521727446280233899)
    ·
      refine ⟨105392520782591169420350849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70261680521727446280233899 105392520782591169420350849)
      ·
        refine ⟨79044390586943377065263137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105392520782591169420350849 79044390586943377065263137)
        ·
          refine ⟨59283292940207532798947353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79044390586943377065263137 59283292940207532798947353)
          ·
            refine ⟨44462469705155649599210515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59283292940207532798947353 44462469705155649599210515)
            ·
              refine ⟨66693704557733474398815773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44462469705155649599210515 66693704557733474398815773)
              ·
                refine ⟨25010139209150052899555915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66693704557733474398815773 25010139209150052899555915)
                ·
                  refine ⟨37515208813725079349333873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25010139209150052899555915 37515208813725079349333873)
                  ·
                    refine ⟨28136406610293809512000405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37515208813725079349333873 28136406610293809512000405)
                    ·
                      refine ⟨1318894059857522320875019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28136406610293809512000405 1318894059857522320875019)
                      ·
                        rfl

theorem cell23_2568537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_2568537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568537 prefixEnd_2568537 := by exact prefixLift 2568537
  have htrace : WordTrace (prefixWord ++ tailWord_2568537) baseStart_2568537 baseEnd_2568537 := by
    simpa [prefixWord, tailWord_2568537, baseEnd_2568537] using wordTrace_append hprefix tailTrace_2568537
  have hstable : (prefixWord ++ tailWord_2568537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568537).length < 2 ^ (prefixWord ++ tailWord_2568537).sum := by decide
  have hdescent : baseEnd_2568537 < baseStart_2568537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568571 : List Nat := [1, 1, 1, 1, 1, 8, 1, 1, 1, 5, 2]
def baseStart_2568571 : Nat := 118140960795 + 2568571 * 2 ^ 59
def prefixEnd_2568571 : Nat := 4983230072969 + 3 ^ 40 * 2568571 * 2
def baseEnd_2568571 : Nat := 1318911518199775187849863

theorem tailTrace_2568571 : CollatzResearch.WordTrace tailWord_2568571 prefixEnd_2568571 1318911518199775187849863 := by
  unfold tailWord_2568571
  simp only [CollatzResearch.WordTrace]
  refine ⟨93683480777513418847049567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62455653851675612564699711 93683480777513418847049567)
  ·
    refine ⟨140525221166270128270574351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93683480777513418847049567 140525221166270128270574351)
    ·
      refine ⟨210787831749405192405861527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140525221166270128270574351 210787831749405192405861527)
      ·
        refine ⟨316181747624107788608792291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210787831749405192405861527 316181747624107788608792291)
        ·
          refine ⟨474272621436161682913188437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316181747624107788608792291 474272621436161682913188437)
          ·
            refine ⟨5557882282455019721638927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 474272621436161682913188437 5557882282455019721638927)
            ·
              refine ⟨8336823423682529582458391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5557882282455019721638927 8336823423682529582458391)
              ·
                refine ⟨12505235135523794373687587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8336823423682529582458391 12505235135523794373687587)
                ·
                  refine ⟨18757852703285691560531381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12505235135523794373687587 18757852703285691560531381)
                  ·
                    refine ⟨1758548690933033583799817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18757852703285691560531381 1758548690933033583799817)
                    ·
                      refine ⟨1318911518199775187849863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1758548690933033583799817 1318911518199775187849863)
                      ·
                        rfl

theorem cell23_2568571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 5, 2].length) (baseStart_2568571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568571 prefixEnd_2568571 := by exact prefixLift 2568571
  have htrace : WordTrace (prefixWord ++ tailWord_2568571) baseStart_2568571 baseEnd_2568571 := by
    simpa [prefixWord, tailWord_2568571, baseEnd_2568571] using wordTrace_append hprefix tailTrace_2568571
  have hstable : (prefixWord ++ tailWord_2568571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568571).length < 2 ^ (prefixWord ++ tailWord_2568571).sum := by decide
  have hdescent : baseEnd_2568571 < baseStart_2568571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568611 : List Nat := [1, 1, 1, 4, 1, 6, 1, 1, 1, 6]
def baseStart_2568611 : Nat := 118140960795 + 2568611 * 2 ^ 59
def prefixEnd_2568611 : Nat := 4983230072969 + 3 ^ 40 * 2568611 * 2
def baseEnd_2568611 : Nat := 439644019141985010449893

theorem tailTrace_2568611 : CollatzResearch.WordTrace tailWord_2568611 prefixEnd_2568611 439644019141985010449893 := by
  unfold tailWord_2568611
  simp only [CollatzResearch.WordTrace]
  refine ⟨93684939697368505678505687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62456626464912337119003791 93684939697368505678505687)
  ·
    refine ⟨140527409546052758517758531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93684939697368505678505687 140527409546052758517758531)
    ·
      refine ⟨210791114319079137776637797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140527409546052758517758531 210791114319079137776637797)
      ·
        refine ⟨39523333934827338333119587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 210791114319079137776637797 39523333934827338333119587)
        ·
          refine ⟨59285000902241007499679381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39523333934827338333119587 59285000902241007499679381)
          ·
            refine ⟨2778984417292547226547471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 59285000902241007499679381 2778984417292547226547471)
            ·
              refine ⟨4168476625938820839821207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2778984417292547226547471 4168476625938820839821207)
              ·
                refine ⟨6252714938908231259731811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4168476625938820839821207 6252714938908231259731811)
                ·
                  refine ⟨9379072408362346889597717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6252714938908231259731811 9379072408362346889597717)
                  ·
                    refine ⟨439644019141985010449893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9379072408362346889597717 439644019141985010449893)
                    ·
                      rfl

theorem cell23_2568611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 6].length) (baseStart_2568611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568611 prefixEnd_2568611 := by exact prefixLift 2568611
  have htrace : WordTrace (prefixWord ++ tailWord_2568611) baseStart_2568611 baseEnd_2568611 := by
    simpa [prefixWord, tailWord_2568611, baseEnd_2568611] using wordTrace_append hprefix tailTrace_2568611
  have hstable : (prefixWord ++ tailWord_2568611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568611).length < 2 ^ (prefixWord ++ tailWord_2568611).sum := by decide
  have hdescent : baseEnd_2568611 < baseStart_2568611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568629 : List Nat := [1, 3, 3, 2, 4, 1, 1, 3, 1, 1, 3]
def baseStart_2568629 : Nat := 118140960795 + 2568629 * 2 ^ 59
def prefixEnd_2568629 : Nat := 4983230072969 + 3 ^ 40 * 2568629 * 2
def baseEnd_2568629 : Nat := 1318941300077735960924597

theorem tailTrace_2568629 : CollatzResearch.WordTrace tailWord_2568629 prefixEnd_2568629 1318941300077735960924597 := by
  unfold tailWord_2568629
  simp only [CollatzResearch.WordTrace]
  refine ⟨93685596211303294752660941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62457064140868863168440627 93685596211303294752660941)
  ·
    refine ⟨35132098579238735532247853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93685596211303294752660941 35132098579238735532247853)
    ·
      refine ⟨13174536967214525824592945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35132098579238735532247853 13174536967214525824592945)
      ·
        refine ⟨9880902725410894368444709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13174536967214525824592945 9880902725410894368444709)
        ·
          refine ⟨1852669261014542694083383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9880902725410894368444709 1852669261014542694083383)
          ·
            refine ⟨2779003891521814041125075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1852669261014542694083383 2779003891521814041125075)
            ·
              refine ⟨4168505837282721061687613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2779003891521814041125075 4168505837282721061687613)
              ·
                refine ⟨1563189688981020398132855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4168505837282721061687613 1563189688981020398132855)
                ·
                  refine ⟨2344784533471530597199283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1563189688981020398132855 2344784533471530597199283)
                  ·
                    refine ⟨3517176800207295895798925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2344784533471530597199283 3517176800207295895798925)
                    ·
                      refine ⟨1318941300077735960924597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3517176800207295895798925 1318941300077735960924597)
                      ·
                        rfl

theorem cell23_2568629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_2568629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568629 prefixEnd_2568629 := by exact prefixLift 2568629
  have htrace : WordTrace (prefixWord ++ tailWord_2568629) baseStart_2568629 baseEnd_2568629 := by
    simpa [prefixWord, tailWord_2568629, baseEnd_2568629] using wordTrace_append hprefix tailTrace_2568629
  have hstable : (prefixWord ++ tailWord_2568629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568629).length < 2 ^ (prefixWord ++ tailWord_2568629).sum := by decide
  have hdescent : baseEnd_2568629 < baseStart_2568629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568638 : List Nat := [4, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3]
def baseStart_2568638 : Nat := 118140960795 + 2568638 * 2 ^ 59
def prefixEnd_2568638 : Nat := 4983230072969 + 3 ^ 40 * 2568638 * 2
def baseEnd_2568638 : Nat := 1318945921403626425712055

theorem tailTrace_2568638 : CollatzResearch.WordTrace tailWord_2568638 prefixEnd_2568638 1318945921403626425712055 := by
  unfold tailWord_2568638
  simp only [CollatzResearch.WordTrace]
  refine ⟨11710740558533836161217321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62457282978847126193159045 11710740558533836161217321)
  ·
    refine ⟨8783055418900377120912991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11710740558533836161217321 8783055418900377120912991)
    ·
      refine ⟨13174583128350565681369487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8783055418900377120912991 13174583128350565681369487)
      ·
        refine ⟨19761874692525848522054231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13174583128350565681369487 19761874692525848522054231)
        ·
          refine ⟨29642812038788772783081347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19761874692525848522054231 29642812038788772783081347)
          ·
            refine ⟨44464218058183159174622021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29642812038788772783081347 44464218058183159174622021)
            ·
              refine ⟨8337040885909342345241629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44464218058183159174622021 8337040885909342345241629)
              ·
                refine ⟨3126390332216003379465611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8337040885909342345241629 3126390332216003379465611)
                ·
                  refine ⟨4689585498324005069198417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3126390332216003379465611 4689585498324005069198417)
                  ·
                    refine ⟨3517189123743003801898813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4689585498324005069198417 3517189123743003801898813)
                    ·
                      refine ⟨1318945921403626425712055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3517189123743003801898813 1318945921403626425712055)
                      ·
                        rfl

theorem cell23_2568638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_2568638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568638 prefixEnd_2568638 := by exact prefixLift 2568638
  have htrace : WordTrace (prefixWord ++ tailWord_2568638) baseStart_2568638 baseEnd_2568638 := by
    simpa [prefixWord, tailWord_2568638, baseEnd_2568638] using wordTrace_append hprefix tailTrace_2568638
  have hstable : (prefixWord ++ tailWord_2568638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568638).length < 2 ^ (prefixWord ++ tailWord_2568638).sum := by decide
  have hdescent : baseEnd_2568638 < baseStart_2568638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568652 : List Nat := [2, 2, 1, 4, 3, 2, 1, 1, 3, 2, 2]
def baseStart_2568652 : Nat := 118140960795 + 2568652 * 2 ^ 59
def prefixEnd_2568652 : Nat := 4983230072969 + 3 ^ 40 * 2568652 * 2
def baseEnd_2568652 : Nat := 1318953110132789370936991

theorem tailTrace_2568652 : CollatzResearch.WordTrace tailWord_2568652 prefixEnd_2568652 1318953110132789370936991 := by
  unfold tailWord_2568652
  simp only [CollatzResearch.WordTrace]
  refine ⟨46843217545109984840374105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62457623393479979787165473 46843217545109984840374105)
  ·
    refine ⟨35132413158832488630280579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46843217545109984840374105 35132413158832488630280579)
    ·
      refine ⟨52698619738248732945420869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35132413158832488630280579 52698619738248732945420869)
      ·
        refine ⟨9880991200921637427266413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52698619738248732945420869 9880991200921637427266413)
        ·
          refine ⟨3705371700345614035224905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9880991200921637427266413 3705371700345614035224905)
          ·
            refine ⟨2779028775259210526418679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3705371700345614035224905 2779028775259210526418679)
            ·
              refine ⟨4168543162888815789628019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2779028775259210526418679 4168543162888815789628019)
              ·
                refine ⟨6252814744333223684442029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4168543162888815789628019 6252814744333223684442029)
                ·
                  refine ⟨2344805529124958881665761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6252814744333223684442029 2344805529124958881665761)
                  ·
                    refine ⟨1758604146843719161249321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2344805529124958881665761 1758604146843719161249321)
                    ·
                      refine ⟨1318953110132789370936991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1758604146843719161249321 1318953110132789370936991)
                      ·
                        rfl

theorem cell23_2568652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_2568652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568652 prefixEnd_2568652 := by exact prefixLift 2568652
  have htrace : WordTrace (prefixWord ++ tailWord_2568652) baseStart_2568652 baseEnd_2568652 := by
    simpa [prefixWord, tailWord_2568652, baseEnd_2568652] using wordTrace_append hprefix tailTrace_2568652
  have hstable : (prefixWord ++ tailWord_2568652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568652).length < 2 ^ (prefixWord ++ tailWord_2568652).sum := by decide
  have hdescent : baseEnd_2568652 < baseStart_2568652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568654 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 2, 7]
def baseStart_2568654 : Nat := 118140960795 + 2568654 * 2 ^ 59
def prefixEnd_2568654 : Nat := 4983230072969 + 3 ^ 40 * 2568654 * 2
def baseEnd_2568654 : Nat := 439651379031366121037327

theorem tailTrace_2568654 : CollatzResearch.WordTrace tailWord_2568654 prefixEnd_2568654 439651379031366121037327 := by
  unfold tailWord_2568654
  simp only [CollatzResearch.WordTrace]
  refine ⟨11710813504526590502790127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62457672024141816014880677 11710813504526590502790127)
  ·
    refine ⟨17566220256789885754185191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11710813504526590502790127 17566220256789885754185191)
    ·
      refine ⟨26349330385184828631277787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17566220256789885754185191 26349330385184828631277787)
      ·
        refine ⟨39523995577777242946916681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26349330385184828631277787 39523995577777242946916681)
        ·
          refine ⟨29642996683332932210187511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39523995577777242946916681 29642996683332932210187511)
          ·
            refine ⟨44464495024999398315281267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29642996683332932210187511 44464495024999398315281267)
            ·
              refine ⟨66696742537499097472921901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44464495024999398315281267 66696742537499097472921901)
              ·
                refine ⟨25011278451562161552345713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66696742537499097472921901 25011278451562161552345713)
                ·
                  refine ⟨18758458838671621164259285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25011278451562161552345713 18758458838671621164259285)
                  ·
                    refine ⟨439651379031366121037327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18758458838671621164259285 439651379031366121037327)
                    ·
                      rfl

theorem cell23_2568654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_2568654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568654 prefixEnd_2568654 := by exact prefixLift 2568654
  have htrace : WordTrace (prefixWord ++ tailWord_2568654) baseStart_2568654 baseEnd_2568654 := by
    simpa [prefixWord, tailWord_2568654, baseEnd_2568654] using wordTrace_append hprefix tailTrace_2568654
  have hstable : (prefixWord ++ tailWord_2568654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568654).length < 2 ^ (prefixWord ++ tailWord_2568654).sum := by decide
  have hdescent : baseEnd_2568654 < baseStart_2568654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568658 : List Nat := [3, 2, 2, 4, 1, 1, 2, 8]
def baseStart_2568658 : Nat := 118140960795 + 2568658 * 2 ^ 59
def prefixEnd_2568658 : Nat := 4983230072969 + 3 ^ 40 * 2568658 * 2
def baseEnd_2568658 : Nat := 48850229296915420276369

theorem tailTrace_2568658 : CollatzResearch.WordTrace tailWord_2568658 prefixEnd_2568658 48850229296915420276369 := by
  unfold tailWord_2568658
  simp only [CollatzResearch.WordTrace]
  refine ⟨23421663482049558176366657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62457769285465488470311085 23421663482049558176366657)
  ·
    refine ⟨17566247611537168632274993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23421663482049558176366657 17566247611537168632274993)
    ·
      refine ⟨13174685708652876474206245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17566247611537168632274993 13174685708652876474206245)
      ·
        refine ⟨2470253570372414338913671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13174685708652876474206245 2470253570372414338913671)
        ·
          refine ⟨3705380355558621508370507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2470253570372414338913671 3705380355558621508370507)
          ·
            refine ⟨5558070533337932262555761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3705380355558621508370507 5558070533337932262555761)
            ·
              refine ⟨4168552900003449196916821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5558070533337932262555761 4168552900003449196916821)
              ·
                refine ⟨48850229296915420276369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4168552900003449196916821 48850229296915420276369)
                ·
                  rfl

theorem cell23_2568658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 8].length) (baseStart_2568658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568658 prefixEnd_2568658 := by exact prefixLift 2568658
  have htrace : WordTrace (prefixWord ++ tailWord_2568658) baseStart_2568658 baseEnd_2568658 := by
    simpa [prefixWord, tailWord_2568658, baseEnd_2568658] using wordTrace_append hprefix tailTrace_2568658
  have hstable : (prefixWord ++ tailWord_2568658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568658).length < 2 ^ (prefixWord ++ tailWord_2568658).sum := by decide
  have hdescent : baseEnd_2568658 < baseStart_2568658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568704 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 4]
def baseStart_2568704 : Nat := 118140960795 + 2568704 * 2 ^ 59
def prefixEnd_2568704 : Nat := 4983230072969 + 3 ^ 40 * 2568704 * 2
def baseEnd_2568704 : Nat := 1318979811126823167486751

theorem tailTrace_2568704 : CollatzResearch.WordTrace tailWord_2568704 prefixEnd_2568704 1318979811126823167486751 := by
  unfold tailWord_2568704
  simp only [CollatzResearch.WordTrace]
  refine ⟨46844165843015791280820583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62458887790687721707760777 46844165843015791280820583)
  ·
    refine ⟨70266248764523686921230875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46844165843015791280820583 70266248764523686921230875)
    ·
      refine ⟨105399373146785530381846313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70266248764523686921230875 105399373146785530381846313)
      ·
        refine ⟨79049529860089147786384735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105399373146785530381846313 79049529860089147786384735)
        ·
          refine ⟨118574294790133721679577103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79049529860089147786384735 118574294790133721679577103)
          ·
            refine ⟨177861442185200582519365655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118574294790133721679577103 177861442185200582519365655)
            ·
              refine ⟨266792163277800873779048483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177861442185200582519365655 266792163277800873779048483)
              ·
                refine ⟨400188244916701310668572725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266792163277800873779048483 400188244916701310668572725)
                ·
                  refine ⟨37517647960940747875178693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 400188244916701310668572725 37517647960940747875178693)
                  ·
                    refine ⟨7034558992676390226596005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37517647960940747875178693 7034558992676390226596005)
                    ·
                      refine ⟨1318979811126823167486751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7034558992676390226596005 1318979811126823167486751)
                      ·
                        rfl

theorem cell23_2568704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_2568704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568704 prefixEnd_2568704 := by exact prefixLift 2568704
  have htrace : WordTrace (prefixWord ++ tailWord_2568704) baseStart_2568704 baseEnd_2568704 := by
    simpa [prefixWord, tailWord_2568704, baseEnd_2568704] using wordTrace_append hprefix tailTrace_2568704
  have hstable : (prefixWord ++ tailWord_2568704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568704).length < 2 ^ (prefixWord ++ tailWord_2568704).sum := by decide
  have hdescent : baseEnd_2568704 < baseStart_2568704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568725 : List Nat := [1, 3, 2, 1, 3, 1, 1, 5, 2, 2, 2]
def baseStart_2568725 : Nat := 118140960795 + 2568725 * 2 ^ 59
def prefixEnd_2568725 : Nat := 4983230072969 + 3 ^ 40 * 2568725 * 2
def baseEnd_2568725 : Nat := 1318990594220567585324155

theorem tailTrace_2568725 : CollatzResearch.WordTrace tailWord_2568725 prefixEnd_2568725 1318990594220567585324155 := by
  unfold tailWord_2568725
  simp only [CollatzResearch.WordTrace]
  refine ⟨93689097618955503148155629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62459398412637002098770419 93689097618955503148155629)
  ·
    refine ⟨35133411607108313680558361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93689097618955503148155629 35133411607108313680558361)
    ·
      refine ⟨26350058705331235260418771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35133411607108313680558361 26350058705331235260418771)
      ·
        refine ⟨39525088057996852890628157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26350058705331235260418771 39525088057996852890628157)
        ·
          refine ⟨14821908021748819833985559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39525088057996852890628157 14821908021748819833985559)
          ·
            refine ⟨22232862032623229750978339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14821908021748819833985559 22232862032623229750978339)
            ·
              refine ⟨33349293048934844626467509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22232862032623229750978339 33349293048934844626467509)
              ·
                refine ⟨3126496223337641683731329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33349293048934844626467509 3126496223337641683731329)
                ·
                  refine ⟨2344872167503231262798497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3126496223337641683731329 2344872167503231262798497)
                  ·
                    refine ⟨1758654125627423447098873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2344872167503231262798497 1758654125627423447098873)
                    ·
                      refine ⟨1318990594220567585324155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1758654125627423447098873 1318990594220567585324155)
                      ·
                        rfl

theorem cell23_2568725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 2, 2, 2].length) (baseStart_2568725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568725 prefixEnd_2568725 := by exact prefixLift 2568725
  have htrace : WordTrace (prefixWord ++ tailWord_2568725) baseStart_2568725 baseEnd_2568725 := by
    simpa [prefixWord, tailWord_2568725, baseEnd_2568725] using wordTrace_append hprefix tailTrace_2568725
  have hstable : (prefixWord ++ tailWord_2568725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568725).length < 2 ^ (prefixWord ++ tailWord_2568725).sum := by decide
  have hdescent : baseEnd_2568725 < baseStart_2568725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568761 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 4, 5]
def baseStart_2568761 : Nat := 118140960795 + 2568761 * 2 ^ 59
def prefixEnd_2568761 : Nat := 4983230072969 + 3 ^ 40 * 2568761 * 2
def baseEnd_2568761 : Nat := 439669693174709814824663

theorem tailTrace_2568761 : CollatzResearch.WordTrace tailWord_2568761 prefixEnd_2568761 439669693174709814824663 := by
  unfold tailWord_2568761
  simp only [CollatzResearch.WordTrace]
  refine ⟨93690410646825081296466137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62460273764550054197644091 93690410646825081296466137)
  ·
    refine ⟨70267807985118810972349603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93690410646825081296466137 70267807985118810972349603)
    ·
      refine ⟨105401711977678216458524405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70267807985118810972349603 105401711977678216458524405)
      ·
        refine ⟨9881410497907332792986663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105401711977678216458524405 9881410497907332792986663)
        ·
          refine ⟨14822115746860999189479995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9881410497907332792986663 14822115746860999189479995)
          ·
            refine ⟨22233173620291498784219993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14822115746860999189479995 22233173620291498784219993)
            ·
              refine ⟨16674880215218624088164995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22233173620291498784219993 16674880215218624088164995)
              ·
                refine ⟨25012320322827936132247493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16674880215218624088164995 25012320322827936132247493)
                ·
                  refine ⟨4689810060530238024796405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25012320322827936132247493 4689810060530238024796405)
                  ·
                    refine ⟨439669693174709814824663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4689810060530238024796405 439669693174709814824663)
                    ·
                      rfl

theorem cell23_2568761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 5].length) (baseStart_2568761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568761 prefixEnd_2568761 := by exact prefixLift 2568761
  have htrace : WordTrace (prefixWord ++ tailWord_2568761) baseStart_2568761 baseEnd_2568761 := by
    simpa [prefixWord, tailWord_2568761, baseEnd_2568761] using wordTrace_append hprefix tailTrace_2568761
  have hstable : (prefixWord ++ tailWord_2568761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568761).length < 2 ^ (prefixWord ++ tailWord_2568761).sum := by decide
  have hdescent : baseEnd_2568761 < baseStart_2568761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568825 : List Nat := [1, 2, 1, 3, 3, 4, 1, 1, 3, 4]
def baseStart_2568825 : Nat := 118140960795 + 2568825 * 2 ^ 59
def prefixEnd_2568825 : Nat := 4983230072969 + 3 ^ 40 * 2568825 * 2
def baseEnd_2568825 : Nat := 439680647428672398024565

theorem tailTrace_2568825 : CollatzResearch.WordTrace tailWord_2568825 prefixEnd_2568825 439680647428672398024565 := by
  unfold tailWord_2568825
  simp only [CollatzResearch.WordTrace]
  refine ⟨93692744918593220226795929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62461829945728813484530619 93692744918593220226795929)
  ·
    refine ⟨70269558688944915170096947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93692744918593220226795929 70269558688944915170096947)
    ·
      refine ⟨105404338033417372755145421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70269558688944915170096947 105404338033417372755145421)
      ·
        refine ⟨39526626762531514783179533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105404338033417372755145421 39526626762531514783179533)
        ·
          refine ⟨14822485035949318043692325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39526626762531514783179533 14822485035949318043692325)
          ·
            refine ⟨2779215944240497133192311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14822485035949318043692325 2779215944240497133192311)
            ·
              refine ⟨4168823916360745699788467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2779215944240497133192311 4168823916360745699788467)
              ·
                refine ⟨6253235874541118549682701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4168823916360745699788467 6253235874541118549682701)
                ·
                  refine ⟨2344963452952919456131013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6253235874541118549682701 2344963452952919456131013)
                  ·
                    refine ⟨439680647428672398024565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2344963452952919456131013 439680647428672398024565)
                    ·
                      rfl

theorem cell23_2568825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 3, 4].length) (baseStart_2568825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568825 prefixEnd_2568825 := by exact prefixLift 2568825
  have htrace : WordTrace (prefixWord ++ tailWord_2568825) baseStart_2568825 baseEnd_2568825 := by
    simpa [prefixWord, tailWord_2568825, baseEnd_2568825] using wordTrace_append hprefix tailTrace_2568825
  have hstable : (prefixWord ++ tailWord_2568825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568825).length < 2 ^ (prefixWord ++ tailWord_2568825).sum := by decide
  have hdescent : baseEnd_2568825 < baseStart_2568825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568831 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 2, 5, 3]
def baseStart_2568831 : Nat := 118140960795 + 2568831 * 2 ^ 59
def prefixEnd_2568831 : Nat := 4983230072969 + 3 ^ 40 * 2568831 * 2
def baseEnd_2568831 : Nat := 1319045023169944170598667

theorem tailTrace_2568831 : CollatzResearch.WordTrace tailWord_2568831 prefixEnd_2568831 1319045023169944170598667 := by
  unfold tailWord_2568831
  simp only [CollatzResearch.WordTrace]
  refine ⟨93692963756571483251514347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62461975837714322167676231 93692963756571483251514347)
  ·
    refine ⟨140539445634857224877271521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93692963756571483251514347 140539445634857224877271521)
    ·
      refine ⟨105404584226142918657953641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140539445634857224877271521 105404584226142918657953641)
      ·
        refine ⟨79053438169607188993465231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105404584226142918657953641 79053438169607188993465231)
        ·
          refine ⟨118580157254410783490197847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79053438169607188993465231 118580157254410783490197847)
          ·
            refine ⟨177870235881616175235296771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118580157254410783490197847 177870235881616175235296771)
            ·
              refine ⟨266805353822424262852945157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177870235881616175235296771 266805353822424262852945157)
              ·
                refine ⟨50026003841704549284927217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 266805353822424262852945157 50026003841704549284927217)
                ·
                  refine ⟨37519502881278411963695413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50026003841704549284927217 37519502881278411963695413)
                  ·
                    refine ⟨3517453395119851121596445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37519502881278411963695413 3517453395119851121596445)
                    ·
                      refine ⟨1319045023169944170598667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3517453395119851121596445 1319045023169944170598667)
                      ·
                        rfl

theorem cell23_2568831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 5, 3].length) (baseStart_2568831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568831 prefixEnd_2568831 := by exact prefixLift 2568831
  have htrace : WordTrace (prefixWord ++ tailWord_2568831) baseStart_2568831 baseEnd_2568831 := by
    simpa [prefixWord, tailWord_2568831, baseEnd_2568831] using wordTrace_append hprefix tailTrace_2568831
  have hstable : (prefixWord ++ tailWord_2568831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568831).length < 2 ^ (prefixWord ++ tailWord_2568831).sum := by decide
  have hdescent : baseEnd_2568831 < baseStart_2568831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568851 : List Nat := [1, 1, 1, 2, 1, 2, 2, 5, 3, 5]
def baseStart_2568851 : Nat := 118140960795 + 2568851 * 2 ^ 59
def prefixEnd_2568851 : Nat := 4983230072969 + 3 ^ 40 * 2568851 * 2
def baseEnd_2568851 : Nat := 439685097594344697449525

theorem tailTrace_2568851 : CollatzResearch.WordTrace tailWord_2568851 prefixEnd_2568851 439685097594344697449525 := by
  unfold tailWord_2568851
  simp only [CollatzResearch.WordTrace]
  refine ⟨93693693216499026667242407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62462462144332684444828271 93693693216499026667242407)
  ·
    refine ⟨140540539824748540000863611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93693693216499026667242407 140540539824748540000863611)
    ·
      refine ⟨210810809737122810001295417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140540539824748540000863611 210810809737122810001295417)
      ·
        refine ⟨158108107302842107500971563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210810809737122810001295417 158108107302842107500971563)
        ·
          refine ⟨237162160954263161251457345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158108107302842107500971563 237162160954263161251457345)
          ·
            refine ⟨177871620715697370938593009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237162160954263161251457345 177871620715697370938593009)
            ·
              refine ⟨133403715536773028203944757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177871620715697370938593009 133403715536773028203944757)
              ·
                refine ⟨12506598331572471394119821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133403715536773028203944757 12506598331572471394119821)
                ·
                  refine ⟨4689974374339676772794933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12506598331572471394119821 4689974374339676772794933)
                  ·
                    refine ⟨439685097594344697449525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4689974374339676772794933 439685097594344697449525)
                    ·
                      rfl

theorem cell23_2568851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 5].length) (baseStart_2568851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568851 prefixEnd_2568851 := by exact prefixLift 2568851
  have htrace : WordTrace (prefixWord ++ tailWord_2568851) baseStart_2568851 baseEnd_2568851 := by
    simpa [prefixWord, tailWord_2568851, baseEnd_2568851] using wordTrace_append hprefix tailTrace_2568851
  have hstable : (prefixWord ++ tailWord_2568851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568851).length < 2 ^ (prefixWord ++ tailWord_2568851).sum := by decide
  have hdescent : baseEnd_2568851 < baseStart_2568851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568852 : List Nat := [2, 4, 2, 2, 1, 2, 2, 1, 2, 2, 3]
def baseStart_2568852 : Nat := 118140960795 + 2568852 * 2 ^ 59
def prefixEnd_2568852 : Nat := 4983230072969 + 3 ^ 40 * 2568852 * 2
def baseEnd_2568852 : Nat := 1319055806263688588436071

theorem tailTrace_2568852 : CollatzResearch.WordTrace tailWord_2568852 prefixEnd_2568852 1319055806263688588436071 := by
  unfold tailWord_2568852
  simp only [CollatzResearch.WordTrace]
  refine ⟨46846864844747701919014405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62462486459663602558685873 46846864844747701919014405)
  ·
    refine ⟨8783787158390194109815201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46846864844747701919014405 8783787158390194109815201)
    ·
      refine ⟨6587840368792645582361401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8783787158390194109815201 6587840368792645582361401)
      ·
        refine ⟨4940880276594484186771051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6587840368792645582361401 4940880276594484186771051)
        ·
          refine ⟨7411320414891726280156577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4940880276594484186771051 7411320414891726280156577)
          ·
            refine ⟨5558490311168794710117433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7411320414891726280156577 5558490311168794710117433)
            ·
              refine ⟨4168867733376596032588075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5558490311168794710117433 4168867733376596032588075)
              ·
                refine ⟨6253301600064894048882113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4168867733376596032588075 6253301600064894048882113)
                ·
                  refine ⟨4689976200048670536661585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6253301600064894048882113 4689976200048670536661585)
                  ·
                    refine ⟨3517482150036502902496189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4689976200048670536661585 3517482150036502902496189)
                    ·
                      refine ⟨1319055806263688588436071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3517482150036502902496189 1319055806263688588436071)
                      ·
                        rfl

theorem cell23_2568852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_2568852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568852 prefixEnd_2568852 := by exact prefixLift 2568852
  have htrace : WordTrace (prefixWord ++ tailWord_2568852) baseStart_2568852 baseEnd_2568852 := by
    simpa [prefixWord, tailWord_2568852, baseEnd_2568852] using wordTrace_append hprefix tailTrace_2568852
  have hstable : (prefixWord ++ tailWord_2568852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568852).length < 2 ^ (prefixWord ++ tailWord_2568852).sum := by decide
  have hdescent : baseEnd_2568852 < baseStart_2568852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568888 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 4, 6, 2]
def baseStart_2568888 : Nat := 118140960795 + 2568888 * 2 ^ 59
def prefixEnd_2568888 : Nat := 4983230072969 + 3 ^ 40 * 2568888 * 2
def baseEnd_2568888 : Nat := 1319074291567250447585905

theorem tailTrace_2568888 : CollatzResearch.WordTrace tailWord_2568888 prefixEnd_2568888 1319074291567250447585905 := by
  unfold tailWord_2568888
  simp only [CollatzResearch.WordTrace]
  refine ⟨46847521358682490993169659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62463361811576654657559545 46847521358682490993169659)
  ·
    refine ⟨70271282038023736489754489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46847521358682490993169659 70271282038023736489754489)
    ·
      refine ⟨52703461528517802367315867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70271282038023736489754489 52703461528517802367315867)
      ·
        refine ⟨79055192292776703550973801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52703461528517802367315867 79055192292776703550973801)
        ·
          refine ⟨59291394219582527663230351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79055192292776703550973801 59291394219582527663230351)
          ·
            refine ⟨88937091329373791494845527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59291394219582527663230351 88937091329373791494845527)
            ·
              refine ⟨133405636994060687242268291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88937091329373791494845527 133405636994060687242268291)
              ·
                refine ⟨200108455491091030863402437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133405636994060687242268291 200108455491091030863402437)
                ·
                  refine ⟨37520335404579568286887957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 200108455491091030863402437 37520335404579568286887957)
                  ·
                    refine ⟨1758765722089667263447873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37520335404579568286887957 1758765722089667263447873)
                    ·
                      refine ⟨1319074291567250447585905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1758765722089667263447873 1319074291567250447585905)
                      ·
                        rfl

theorem cell23_2568888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 4, 6, 2].length) (baseStart_2568888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568888 prefixEnd_2568888 := by exact prefixLift 2568888
  have htrace : WordTrace (prefixWord ++ tailWord_2568888) baseStart_2568888 baseEnd_2568888 := by
    simpa [prefixWord, tailWord_2568888, baseEnd_2568888] using wordTrace_append hprefix tailTrace_2568888
  have hstable : (prefixWord ++ tailWord_2568888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568888).length < 2 ^ (prefixWord ++ tailWord_2568888).sum := by decide
  have hdescent : baseEnd_2568888 < baseStart_2568888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568909 : List Nat := [1, 6, 2, 1, 2, 1, 1, 1, 1, 5, 2]
def baseStart_2568909 : Nat := 118140960795 + 2568909 * 2 ^ 59
def prefixEnd_2568909 : Nat := 4983230072969 + 3 ^ 40 * 2568909 * 2
def baseEnd_2568909 : Nat := 1319085074660994865423309

theorem tailTrace_2568909 : CollatzResearch.WordTrace tailWord_2568909 prefixEnd_2568909 1319085074660994865423309 := by
  unfold tailWord_2568909
  simp only [CollatzResearch.WordTrace]
  refine ⟨93695808650288902572853781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62463872433525935048569187 93695808650288902572853781)
  ·
    refine ⟨4391991030482292308102521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 93695808650288902572853781 4391991030482292308102521)
    ·
      refine ⟨3293993272861719231076891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4391991030482292308102521 3293993272861719231076891)
      ·
        refine ⟨4940989909292578846615337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3293993272861719231076891 4940989909292578846615337)
        ·
          refine ⟨3705742431969434134961503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4940989909292578846615337 3705742431969434134961503)
          ·
            refine ⟨5558613647954151202442255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3705742431969434134961503 5558613647954151202442255)
            ·
              refine ⟨8337920471931226803663383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5558613647954151202442255 8337920471931226803663383)
              ·
                refine ⟨12506880707896840205495075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8337920471931226803663383 12506880707896840205495075)
                ·
                  refine ⟨18760321061845260308242613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12506880707896840205495075 18760321061845260308242613)
                  ·
                    refine ⟨1758780099547993153897745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18760321061845260308242613 1758780099547993153897745)
                    ·
                      refine ⟨1319085074660994865423309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1758780099547993153897745 1319085074660994865423309)
                      ·
                        rfl

theorem cell23_2568909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_2568909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568909 prefixEnd_2568909 := by exact prefixLift 2568909
  have htrace : WordTrace (prefixWord ++ tailWord_2568909) baseStart_2568909 baseEnd_2568909 := by
    simpa [prefixWord, tailWord_2568909, baseEnd_2568909] using wordTrace_append hprefix tailTrace_2568909
  have hstable : (prefixWord ++ tailWord_2568909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568909).length < 2 ^ (prefixWord ++ tailWord_2568909).sum := by decide
  have hdescent : baseEnd_2568909 < baseStart_2568909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568916 : List Nat := [2, 4, 1, 3, 2, 1, 2, 3, 1, 1, 3]
def baseStart_2568916 : Nat := 118140960795 + 2568916 * 2 ^ 59
def prefixEnd_2568916 : Nat := 4983230072969 + 3 ^ 40 * 2568916 * 2
def baseEnd_2568916 : Nat := 1319088669025576338035777

theorem tailTrace_2568916 : CollatzResearch.WordTrace tailWord_2568916 prefixEnd_2568916 1319088669025576338035777 := by
  unfold tailWord_2568916
  simp only [CollatzResearch.WordTrace]
  refine ⟨46848031980631771384179301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62464042640842361845572401 46848031980631771384179301)
  ·
    refine ⟨8784005996368457134533619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46848031980631771384179301 8784005996368457134533619)
    ·
      refine ⟨13176008994552685701800429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8784005996368457134533619 13176008994552685701800429)
      ·
        refine ⟨4941003372957257138175161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13176008994552685701800429 4941003372957257138175161)
        ·
          refine ⟨3705752529717942853631371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4941003372957257138175161 3705752529717942853631371)
          ·
            refine ⟨5558628794576914280447057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3705752529717942853631371 5558628794576914280447057)
            ·
              refine ⟨4168971595932685710335293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5558628794576914280447057 4168971595932685710335293)
              ·
                refine ⟨1563364348474757141375735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4168971595932685710335293 1563364348474757141375735)
                ·
                  refine ⟨2345046522712135712063603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1563364348474757141375735 2345046522712135712063603)
                  ·
                    refine ⟨3517569784068203568095405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2345046522712135712063603 3517569784068203568095405)
                    ·
                      refine ⟨1319088669025576338035777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3517569784068203568095405 1319088669025576338035777)
                      ·
                        rfl

theorem cell23_2568916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_2568916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568916 prefixEnd_2568916 := by exact prefixLift 2568916
  have htrace : WordTrace (prefixWord ++ tailWord_2568916) baseStart_2568916 baseEnd_2568916 := by
    simpa [prefixWord, tailWord_2568916, baseEnd_2568916] using wordTrace_append hprefix tailTrace_2568916
  have hstable : (prefixWord ++ tailWord_2568916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568916).length < 2 ^ (prefixWord ++ tailWord_2568916).sum := by decide
  have hdescent : baseEnd_2568916 < baseStart_2568916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568932 : List Nat := [2, 3, 1, 1, 1, 6, 1, 2, 2, 4]
def baseStart_2568932 : Nat := 118140960795 + 2568932 * 2 ^ 59
def prefixEnd_2568932 : Nat := 4983230072969 + 3 ^ 40 * 2568932 * 2
def baseEnd_2568932 : Nat := 439698961572016091811901

theorem tailTrace_2568932 : CollatzResearch.WordTrace tailWord_2568932 prefixEnd_2568932 439698961572016091811901 := by
  unfold tailWord_2568932
  simp only [CollatzResearch.WordTrace]
  refine ⟨46848323764602788750470525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62464431686137051667294033 46848323764602788750470525)
  ·
    refine ⟨17568121411726045781426447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46848323764602788750470525 17568121411726045781426447)
    ·
      refine ⟨26352182117589068672139671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17568121411726045781426447 26352182117589068672139671)
      ·
        refine ⟨39528273176383603008209507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26352182117589068672139671 39528273176383603008209507)
        ·
          refine ⟨59292409764575404512314261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39528273176383603008209507 59292409764575404512314261)
          ·
            refine ⟨2779331707714472086514731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 59292409764575404512314261 2779331707714472086514731)
            ·
              refine ⟨4168997561571708129772097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2779331707714472086514731 4168997561571708129772097)
              ·
                refine ⟨3126748171178781097329073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4168997561571708129772097 3126748171178781097329073)
                ·
                  refine ⟨2345061128384085822996805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3126748171178781097329073 2345061128384085822996805)
                  ·
                    refine ⟨439698961572016091811901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2345061128384085822996805 439698961572016091811901)
                    ·
                      rfl

theorem cell23_2568932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_2568932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568932 prefixEnd_2568932 := by exact prefixLift 2568932
  have htrace : WordTrace (prefixWord ++ tailWord_2568932) baseStart_2568932 baseEnd_2568932 := by
    simpa [prefixWord, tailWord_2568932, baseEnd_2568932] using wordTrace_append hprefix tailTrace_2568932
  have hstable : (prefixWord ++ tailWord_2568932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568932).length < 2 ^ (prefixWord ++ tailWord_2568932).sum := by decide
  have hdescent : baseEnd_2568932 < baseStart_2568932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568962 : List Nat := [3, 4, 1, 1, 1, 4, 2, 7]
def baseStart_2568962 : Nat := 118140960795 + 2568962 * 2 ^ 59
def prefixEnd_2568962 : Nat := 4983230072969 + 3 ^ 40 * 2568962 * 2
def baseEnd_2568962 : Nat := 48856010708729005854095

theorem tailTrace_2568962 : CollatzResearch.WordTrace tailWord_2568962 prefixEnd_2568962 48856010708729005854095 := by
  unfold tailWord_2568962
  simp only [CollatzResearch.WordTrace]
  refine ⟨23424435429774223156133285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62465161146064595083022093 23424435429774223156133285)
  ·
    refine ⟨4392081643082666841774991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23424435429774223156133285 4392081643082666841774991)
    ·
      refine ⟨6588122464624000262662487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4392081643082666841774991 6588122464624000262662487)
      ·
        refine ⟨9882183696936000393993731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6588122464624000262662487 9882183696936000393993731)
        ·
          refine ⟨14823275545404000590990597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9882183696936000393993731 14823275545404000590990597)
          ·
            refine ⟨2779364164763250110810737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14823275545404000590990597 2779364164763250110810737)
            ·
              refine ⟨2084523123572437583108053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2779364164763250110810737 2084523123572437583108053)
              ·
                refine ⟨48856010708729005854095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2084523123572437583108053 48856010708729005854095)
                ·
                  rfl

theorem cell23_2568962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 7].length) (baseStart_2568962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568962 prefixEnd_2568962 := by exact prefixLift 2568962
  have htrace : WordTrace (prefixWord ++ tailWord_2568962) baseStart_2568962 baseEnd_2568962 := by
    simpa [prefixWord, tailWord_2568962, baseEnd_2568962] using wordTrace_append hprefix tailTrace_2568962
  have hstable : (prefixWord ++ tailWord_2568962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568962).length < 2 ^ (prefixWord ++ tailWord_2568962).sum := by decide
  have hdescent : baseEnd_2568962 < baseStart_2568962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568965 : List Nat := [1, 3, 1, 1, 2, 1, 1, 5, 3, 3, 2]
def baseStart_2568965 : Nat := 118140960795 + 2568965 * 2 ^ 59
def prefixEnd_2568965 : Nat := 4983230072969 + 3 ^ 40 * 2568965 * 2
def baseEnd_2568965 : Nat := 1319113829577646646323051

theorem tailTrace_2568965 : CollatzResearch.WordTrace tailWord_2568965 prefixEnd_2568965 1319113829577646646323051 := by
  unfold tailWord_2568965
  simp only [CollatzResearch.WordTrace]
  refine ⟨93697851138086024136892349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62465234092057349424594899 93697851138086024136892349)
  ·
    refine ⟨35136694176782259051334631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93697851138086024136892349 35136694176782259051334631)
    ·
      refine ⟨52705041265173388577001947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35136694176782259051334631 52705041265173388577001947)
      ·
        refine ⟨79057561897760082865502921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52705041265173388577001947 79057561897760082865502921)
        ·
          refine ⟨59293171423320062149127191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79057561897760082865502921 59293171423320062149127191)
          ·
            refine ⟨88939757134980093223690787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59293171423320062149127191 88939757134980093223690787)
            ·
              refine ⟨133409635702470139835536181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88939757134980093223690787 133409635702470139835536181)
              ·
                refine ⟨12507153347106575609581517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133409635702470139835536181 12507153347106575609581517)
                ·
                  refine ⟨4690182505164965853593069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12507153347106575609581517 4690182505164965853593069)
                  ·
                    refine ⟨1758818439436862195097401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4690182505164965853593069 1758818439436862195097401)
                    ·
                      refine ⟨1319113829577646646323051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1758818439436862195097401 1319113829577646646323051)
                      ·
                        rfl

theorem cell23_2568965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 3, 2].length) (baseStart_2568965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568965 prefixEnd_2568965 := by exact prefixLift 2568965
  have htrace : WordTrace (prefixWord ++ tailWord_2568965) baseStart_2568965 baseEnd_2568965 := by
    simpa [prefixWord, tailWord_2568965, baseEnd_2568965] using wordTrace_append hprefix tailTrace_2568965
  have hstable : (prefixWord ++ tailWord_2568965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568965).length < 2 ^ (prefixWord ++ tailWord_2568965).sum := by decide
  have hdescent : baseEnd_2568965 < baseStart_2568965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2568968 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 2, 2, 5]
def baseStart_2568968 : Nat := 118140960795 + 2568968 * 2 ^ 59
def prefixEnd_2568968 : Nat := 4983230072969 + 3 ^ 40 * 2568968 * 2
def baseEnd_2568968 : Nat := 1319115370019610134585537

theorem tailTrace_2568968 : CollatzResearch.WordTrace tailWord_2568968 prefixEnd_2568968 1319115370019610134585537 := by
  unfold tailWord_2568968
  simp only [CollatzResearch.WordTrace]
  refine ⟨46848980278537577824625779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62465307038050103766167705 46848980278537577824625779)
  ·
    refine ⟨70273470417806366736938669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46848980278537577824625779 70273470417806366736938669)
    ·
      refine ⟨26352551406677387526352001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70273470417806366736938669 26352551406677387526352001)
      ·
        refine ⟨19764413555008040644764001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26352551406677387526352001 19764413555008040644764001)
        ·
          refine ⟨14823310166256030483573001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19764413555008040644764001 14823310166256030483573001)
          ·
            refine ⟨11117482624692022862679751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14823310166256030483573001 11117482624692022862679751)
            ·
              refine ⟨16676223937038034294019627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11117482624692022862679751 16676223937038034294019627)
              ·
                refine ⟨25014335905557051441029441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16676223937038034294019627 25014335905557051441029441)
                ·
                  refine ⟨18760751929167788580772081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25014335905557051441029441 18760751929167788580772081)
                  ·
                    refine ⟨14070563946875841435579061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18760751929167788580772081 14070563946875841435579061)
                    ·
                      refine ⟨1319115370019610134585537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14070563946875841435579061 1319115370019610134585537)
                      ·
                        rfl

theorem cell23_2568968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_2568968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2568968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2568968 prefixEnd_2568968 := by exact prefixLift 2568968
  have htrace : WordTrace (prefixWord ++ tailWord_2568968) baseStart_2568968 baseEnd_2568968 := by
    simpa [prefixWord, tailWord_2568968, baseEnd_2568968] using wordTrace_append hprefix tailTrace_2568968
  have hstable : (prefixWord ++ tailWord_2568968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2568968).length < 2 ^ (prefixWord ++ tailWord_2568968).sum := by decide
  have hdescent : baseEnd_2568968 < baseStart_2568968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2568968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569006 : List Nat := [4, 1, 3, 2, 1, 1, 4, 1, 2, 1, 3]
def baseStart_2569006 : Nat := 118140960795 + 2569006 * 2 ^ 59
def prefixEnd_2569006 : Nat := 4983230072969 + 3 ^ 40 * 2569006 * 2
def baseEnd_2569006 : Nat := 1319134882284480985910363

theorem tailTrace_2569006 : CollatzResearch.WordTrace tailWord_2569006 prefixEnd_2569006 1319134882284480985910363 := by
  unfold tailWord_2569006
  simp only [CollatzResearch.WordTrace]
  refine ⟨11712418316367186017391859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62466231020624992092756581 11712418316367186017391859)
  ·
    refine ⟨17568627474550779026087789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11712418316367186017391859 17568627474550779026087789)
    ·
      refine ⟨6588235302956542134782921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17568627474550779026087789 6588235302956542134782921)
      ·
        refine ⟨4941176477217406601087191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6588235302956542134782921 4941176477217406601087191)
        ·
          refine ⟨7411764715826109901630787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4941176477217406601087191 7411764715826109901630787)
          ·
            refine ⟨11117647073739164852446181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7411764715826109901630787 11117647073739164852446181)
            ·
              refine ⟨2084558826326093409833659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11117647073739164852446181 2084558826326093409833659)
              ·
                refine ⟨3126838239489140114750489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2084558826326093409833659 3126838239489140114750489)
                ·
                  refine ⟨2345128679616855086062867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3126838239489140114750489 2345128679616855086062867)
                  ·
                    refine ⟨3517693019425282629094301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2345128679616855086062867 3517693019425282629094301)
                    ·
                      refine ⟨1319134882284480985910363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3517693019425282629094301 1319134882284480985910363)
                      ·
                        rfl

theorem cell23_2569006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_2569006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569006 prefixEnd_2569006 := by exact prefixLift 2569006
  have htrace : WordTrace (prefixWord ++ tailWord_2569006) baseStart_2569006 baseEnd_2569006 := by
    simpa [prefixWord, tailWord_2569006, baseEnd_2569006] using wordTrace_append hprefix tailTrace_2569006
  have hstable : (prefixWord ++ tailWord_2569006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569006).length < 2 ^ (prefixWord ++ tailWord_2569006).sum := by decide
  have hdescent : baseEnd_2569006 < baseStart_2569006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569008 : List Nat := [2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 4]
def baseStart_2569008 : Nat := 118140960795 + 2569008 * 2 ^ 59
def prefixEnd_2569008 : Nat := 4983230072969 + 3 ^ 40 * 2569008 * 2
def baseEnd_2569008 : Nat := 1319135909245789978085353

theorem tailTrace_2569008 : CollatzResearch.WordTrace tailWord_2569008 prefixEnd_2569008 1319135909245789978085353 := by
  unfold tailWord_2569008
  simp only [CollatzResearch.WordTrace]
  refine ⟨46849709738465121240353839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62466279651286828320471785 46849709738465121240353839)
  ·
    refine ⟨70274564607697681860530759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46849709738465121240353839 70274564607697681860530759)
    ·
      refine ⟨105411846911546522790796139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70274564607697681860530759 105411846911546522790796139)
      ·
        refine ⟨158117770367319784186194209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105411846911546522790796139 158117770367319784186194209)
        ·
          refine ⟨118588327775489838139645657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158117770367319784186194209 118588327775489838139645657)
          ·
            refine ⟨88941245831617378604734243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118588327775489838139645657 88941245831617378604734243)
            ·
              refine ⟨133411868747426067907101365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88941245831617378604734243 133411868747426067907101365)
              ·
                refine ⟨12507362695071193866290753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133411868747426067907101365 12507362695071193866290753)
                ·
                  refine ⟨9380522021303395399718065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12507362695071193866290753 9380522021303395399718065)
                  ·
                    refine ⟨7035391515977546549788549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9380522021303395399718065 7035391515977546549788549)
                    ·
                      refine ⟨1319135909245789978085353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7035391515977546549788549 1319135909245789978085353)
                      ·
                        rfl

theorem cell23_2569008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 4].length) (baseStart_2569008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569008 prefixEnd_2569008 := by exact prefixLift 2569008
  have htrace : WordTrace (prefixWord ++ tailWord_2569008) baseStart_2569008 baseEnd_2569008 := by
    simpa [prefixWord, tailWord_2569008, baseEnd_2569008] using wordTrace_append hprefix tailTrace_2569008
  have hstable : (prefixWord ++ tailWord_2569008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569008).length < 2 ^ (prefixWord ++ tailWord_2569008).sum := by decide
  have hdescent : baseEnd_2569008 < baseStart_2569008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569045 : List Nat := [1, 3, 2, 2, 2, 1, 2, 2, 2, 3, 3]
def baseStart_2569045 : Nat := 118140960795 + 2569045 * 2 ^ 59
def prefixEnd_2569045 : Nat := 4983230072969 + 3 ^ 40 * 2569045 * 2
def baseEnd_2569045 : Nat := 1319154908030006333322683

theorem tailTrace_2569045 : CollatzResearch.WordTrace tailWord_2569045 prefixEnd_2569045 1319154908030006333322683 := by
  unfold tailWord_2569045
  simp only [CollatzResearch.WordTrace]
  refine ⟨93700768977796197799804589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62467179318530798533203059 93700768977796197799804589)
  ·
    refine ⟨35137788366673574174926721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93700768977796197799804589 35137788366673574174926721)
    ·
      refine ⟨26353341275005180631195041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35137788366673574174926721 26353341275005180631195041)
      ·
        refine ⟨19765005956253885473396281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26353341275005180631195041 19765005956253885473396281)
        ·
          refine ⟨14823754467190414105047211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19765005956253885473396281 14823754467190414105047211)
          ·
            refine ⟨22235631700785621157570817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14823754467190414105047211 22235631700785621157570817)
            ·
              refine ⟨16676723775589215868178113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22235631700785621157570817 16676723775589215868178113)
              ·
                refine ⟨12507542831691911901133585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16676723775589215868178113 12507542831691911901133585)
                ·
                  refine ⟨9380657123768933925850189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12507542831691911901133585 9380657123768933925850189)
                  ·
                    refine ⟨3517746421413350222193821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9380657123768933925850189 3517746421413350222193821)
                    ·
                      refine ⟨1319154908030006333322683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3517746421413350222193821 1319154908030006333322683)
                      ·
                        rfl

theorem cell23_2569045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_2569045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569045 prefixEnd_2569045 := by exact prefixLift 2569045
  have htrace : WordTrace (prefixWord ++ tailWord_2569045) baseStart_2569045 baseEnd_2569045 := by
    simpa [prefixWord, tailWord_2569045, baseEnd_2569045] using wordTrace_append hprefix tailTrace_2569045
  have hstable : (prefixWord ++ tailWord_2569045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569045).length < 2 ^ (prefixWord ++ tailWord_2569045).sum := by decide
  have hdescent : baseEnd_2569045 < baseStart_2569045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569055 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 1, 7, 2]
def baseStart_2569055 : Nat := 118140960795 + 2569055 * 2 ^ 59
def prefixEnd_2569055 : Nat := 4983230072969 + 3 ^ 40 * 2569055 * 2
def baseEnd_2569055 : Nat := 1319160042836551294197637

theorem tailTrace_2569055 : CollatzResearch.WordTrace tailWord_2569055 prefixEnd_2569055 1319160042836551294197637 := by
  unfold tailWord_2569055
  simp only [CollatzResearch.WordTrace]
  refine ⟨93701133707759969507668619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62467422471839979671779079 93701133707759969507668619)
  ·
    refine ⟨140551700561639954261502929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93701133707759969507668619 140551700561639954261502929)
    ·
      refine ⟨105413775421229965696127197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140551700561639954261502929 105413775421229965696127197)
      ·
        refine ⟨39530165782961237136047699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105413775421229965696127197 39530165782961237136047699)
        ·
          refine ⟨59295248674441855704071549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39530165782961237136047699 59295248674441855704071549)
          ·
            refine ⟨22235718252915695889026831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59295248674441855704071549 22235718252915695889026831)
            ·
              refine ⟨33353577379373543833540247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22235718252915695889026831 33353577379373543833540247)
              ·
                refine ⟨50030366069060315750310371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33353577379373543833540247 50030366069060315750310371)
                ·
                  refine ⟨75045549103590473625465557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50030366069060315750310371 75045549103590473625465557)
                  ·
                    refine ⟨1758880057115401725596849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 75045549103590473625465557 1758880057115401725596849)
                    ·
                      refine ⟨1319160042836551294197637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1758880057115401725596849 1319160042836551294197637)
                      ·
                        rfl

theorem cell23_2569055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 7, 2].length) (baseStart_2569055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569055 prefixEnd_2569055 := by exact prefixLift 2569055
  have htrace : WordTrace (prefixWord ++ tailWord_2569055) baseStart_2569055 baseEnd_2569055 := by
    simpa [prefixWord, tailWord_2569055, baseEnd_2569055] using wordTrace_append hprefix tailTrace_2569055
  have hstable : (prefixWord ++ tailWord_2569055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569055).length < 2 ^ (prefixWord ++ tailWord_2569055).sum := by decide
  have hdescent : baseEnd_2569055 < baseStart_2569055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569086 : List Nat := [4, 2, 3, 1, 2, 1, 2, 3, 5]
def baseStart_2569086 : Nat := 118140960795 + 2569086 * 2 ^ 59
def prefixEnd_2569086 : Nat := 4983230072969 + 3 ^ 40 * 2569086 * 2
def baseEnd_2569086 : Nat := 146575106748537852545555

theorem tailTrace_2569086 : CollatzResearch.WordTrace tailWord_2569086 prefixEnd_2569086 146575106748537852545555 := by
  unfold tailWord_2569086
  simp only [CollatzResearch.WordTrace]
  refine ⟨11712783046330957725255889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62468176247098441201364741 11712783046330957725255889)
  ·
    refine ⟨8784587284748218293941917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11712783046330957725255889 8784587284748218293941917)
    ·
      refine ⟨3294220231780581860228219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8784587284748218293941917 3294220231780581860228219)
      ·
        refine ⟨4941330347670872790342329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3294220231780581860228219 4941330347670872790342329)
        ·
          refine ⟨3705997760753154592756747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4941330347670872790342329 3705997760753154592756747)
          ·
            refine ⟨5558996641129731889135121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3705997760753154592756747 5558996641129731889135121)
            ·
              refine ⟨4169247480847298916851341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5558996641129731889135121 4169247480847298916851341)
              ·
                refine ⟨1563467805317737093819253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4169247480847298916851341 1563467805317737093819253)
                ·
                  refine ⟨146575106748537852545555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1563467805317737093819253 146575106748537852545555)
                  ·
                    rfl

theorem cell23_2569086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_2569086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569086 prefixEnd_2569086 := by exact prefixLift 2569086
  have htrace : WordTrace (prefixWord ++ tailWord_2569086) baseStart_2569086 baseEnd_2569086 := by
    simpa [prefixWord, tailWord_2569086, baseEnd_2569086] using wordTrace_append hprefix tailTrace_2569086
  have hstable : (prefixWord ++ tailWord_2569086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569086).length < 2 ^ (prefixWord ++ tailWord_2569086).sum := by decide
  have hdescent : baseEnd_2569086 < baseStart_2569086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569088 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 5]
def baseStart_2569088 : Nat := 118140960795 + 2569088 * 2 ^ 59
def prefixEnd_2569088 : Nat := 4983230072969 + 3 ^ 40 * 2569088 * 2
def baseEnd_2569088 : Nat := 1319176987698149665084985

theorem tailTrace_2569088 : CollatzResearch.WordTrace tailWord_2569088 prefixEnd_2569088 1319176987698149665084985 := by
  unfold tailWord_2569088
  simp only [CollatzResearch.WordTrace]
  refine ⟨46851168658320208071809959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62468224877760277429079945 46851168658320208071809959)
  ·
    refine ⟨70276752987480312107714939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46851168658320208071809959 70276752987480312107714939)
    ·
      refine ⟨105415129481220468161572409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70276752987480312107714939 105415129481220468161572409)
      ·
        refine ⟨79061347110915351121179307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105415129481220468161572409 79061347110915351121179307)
        ·
          refine ⟨118592020666373026681768961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79061347110915351121179307 118592020666373026681768961)
          ·
            refine ⟨88944015499779770011326721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118592020666373026681768961 88944015499779770011326721)
            ·
              refine ⟨66708011624834827508495041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88944015499779770011326721 66708011624834827508495041)
              ·
                refine ⟨50031008718626120631371281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66708011624834827508495041 50031008718626120631371281)
                ·
                  refine ⟨37523256538969590473528461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50031008718626120631371281 37523256538969590473528461)
                  ·
                    refine ⟨14071221202113596427573173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37523256538969590473528461 14071221202113596427573173)
                    ·
                      refine ⟨1319176987698149665084985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14071221202113596427573173 1319176987698149665084985)
                      ·
                        rfl

theorem cell23_2569088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_2569088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569088 prefixEnd_2569088 := by exact prefixLift 2569088
  have htrace : WordTrace (prefixWord ++ tailWord_2569088) baseStart_2569088 baseEnd_2569088 := by
    simpa [prefixWord, tailWord_2569088, baseEnd_2569088] using wordTrace_append hprefix tailTrace_2569088
  have hstable : (prefixWord ++ tailWord_2569088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569088).length < 2 ^ (prefixWord ++ tailWord_2569088).sum := by decide
  have hdescent : baseEnd_2569088 < baseStart_2569088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569105 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 3]
def baseStart_2569105 : Nat := 118140960795 + 2569105 * 2 ^ 59
def prefixEnd_2569105 : Nat := 4983230072969 + 3 ^ 40 * 2569105 * 2
def baseEnd_2569105 : Nat := 1319185716869276098572407

theorem tailTrace_2569105 : CollatzResearch.WordTrace tailWord_2569105 prefixEnd_2569105 1319185716869276098572407 := by
  unfold tailWord_2569105
  simp only [CollatzResearch.WordTrace]
  refine ⟨93702957357578828046988769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62468638238385885364659179 93702957357578828046988769)
  ·
    refine ⟨70277218018184121035241577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93702957357578828046988769 70277218018184121035241577)
    ·
      refine ⟨52707913513638090776431183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70277218018184121035241577 52707913513638090776431183)
      ·
        refine ⟨79061870270457136164646775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52707913513638090776431183 79061870270457136164646775)
        ·
          refine ⟨118592805405685704246970163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79061870270457136164646775 118592805405685704246970163)
          ·
            refine ⟨177889208108528556370455245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118592805405685704246970163 177889208108528556370455245)
            ·
              refine ⟨66708453040698208638920717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177889208108528556370455245 66708453040698208638920717)
              ·
                refine ⟨25015669890261828239595269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66708453040698208638920717 25015669890261828239595269)
                ·
                  refine ⟨4690438104424092794924113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25015669890261828239595269 4690438104424092794924113)
                  ·
                    refine ⟨3517828578318069596193085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4690438104424092794924113 3517828578318069596193085)
                    ·
                      refine ⟨1319185716869276098572407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3517828578318069596193085 1319185716869276098572407)
                      ·
                        rfl

theorem cell23_2569105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 3].length) (baseStart_2569105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569105 prefixEnd_2569105 := by exact prefixLift 2569105
  have htrace : WordTrace (prefixWord ++ tailWord_2569105) baseStart_2569105 baseEnd_2569105 := by
    simpa [prefixWord, tailWord_2569105, baseEnd_2569105] using wordTrace_append hprefix tailTrace_2569105
  have hstable : (prefixWord ++ tailWord_2569105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569105).length < 2 ^ (prefixWord ++ tailWord_2569105).sum := by decide
  have hdescent : baseEnd_2569105 < baseStart_2569105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569122 : List Nat := [3, 3, 1, 2, 2, 1, 1, 2, 1, 4, 3]
def baseStart_2569122 : Nat := 118140960795 + 2569122 * 2 ^ 59
def prefixEnd_2569122 : Nat := 4983230072969 + 3 ^ 40 * 2569122 * 2
def baseEnd_2569122 : Nat := 1319194446040402532059829

theorem tailTrace_2569122 : CollatzResearch.WordTrace tailWord_2569122 prefixEnd_2569122 1319194446040402532059829 := by
  unfold tailWord_2569122
  simp only [CollatzResearch.WordTrace]
  refine ⟨23425894349629309987589405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62469051599011493300238413 23425894349629309987589405)
  ·
    refine ⟨8784710381110991245346027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23425894349629309987589405 8784710381110991245346027)
    ·
      refine ⟨13177065571666486868019041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8784710381110991245346027 13177065571666486868019041)
      ·
        refine ⟨9882799178749865151014281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13177065571666486868019041 9882799178749865151014281)
        ·
          refine ⟨7412099384062398863260711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9882799178749865151014281 7412099384062398863260711)
          ·
            refine ⟨11118149076093598294891067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7412099384062398863260711 11118149076093598294891067)
            ·
              refine ⟨16677223614140397442336601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11118149076093598294891067 16677223614140397442336601)
              ·
                refine ⟨12507917710605298081752451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16677223614140397442336601 12507917710605298081752451)
                ·
                  refine ⟨18761876565907947122628677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12507917710605298081752451 18761876565907947122628677)
                  ·
                    refine ⟨3517851856107740085492877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18761876565907947122628677 3517851856107740085492877)
                    ·
                      refine ⟨1319194446040402532059829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3517851856107740085492877 1319194446040402532059829)
                      ·
                        rfl

theorem cell23_2569122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_2569122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569122 prefixEnd_2569122 := by exact prefixLift 2569122
  have htrace : WordTrace (prefixWord ++ tailWord_2569122) baseStart_2569122 baseEnd_2569122 := by
    simpa [prefixWord, tailWord_2569122, baseEnd_2569122] using wordTrace_append hprefix tailTrace_2569122
  have hstable : (prefixWord ++ tailWord_2569122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569122).length < 2 ^ (prefixWord ++ tailWord_2569122).sum := by decide
  have hdescent : baseEnd_2569122 < baseStart_2569122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569156 : List Nat := [2, 3, 3, 3, 1, 1, 1, 2, 2, 2, 3]
def baseStart_2569156 : Nat := 118140960795 + 2569156 * 2 ^ 59
def prefixEnd_2569156 : Nat := 4983230072969 + 3 ^ 40 * 2569156 * 2
def baseEnd_2569156 : Nat := 1319211904382655399034673

theorem tailTrace_2569156 : CollatzResearch.WordTrace tailWord_2569156 prefixEnd_2569156 1319211904382655399034673 := by
  unfold tailWord_2569156
  simp only [CollatzResearch.WordTrace]
  refine ⟨46852408740197031878547661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62469878320262709171396881 46852408740197031878547661)
  ·
    refine ⟨17569653277573886954455373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46852408740197031878547661 17569653277573886954455373)
    ·
      refine ⟨6588619979090207607920765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17569653277573886954455373 6588619979090207607920765)
      ·
        refine ⟨2470732492158827852970287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6588619979090207607920765 2470732492158827852970287)
        ·
          refine ⟨3706098738238241779455431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2470732492158827852970287 3706098738238241779455431)
          ·
            refine ⟨5559148107357362669183147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3706098738238241779455431 5559148107357362669183147)
            ·
              refine ⟨8338722161036044003774721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5559148107357362669183147 8338722161036044003774721)
              ·
                refine ⟨6254041620777033002831041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8338722161036044003774721 6254041620777033002831041)
                ·
                  refine ⟨4690531215582774752123281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6254041620777033002831041 4690531215582774752123281)
                  ·
                    refine ⟨3517898411687081064092461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4690531215582774752123281 3517898411687081064092461)
                    ·
                      refine ⟨1319211904382655399034673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3517898411687081064092461 1319211904382655399034673)
                      ·
                        rfl

theorem cell23_2569156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_2569156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569156 prefixEnd_2569156 := by exact prefixLift 2569156
  have htrace : WordTrace (prefixWord ++ tailWord_2569156) baseStart_2569156 baseEnd_2569156 := by
    simpa [prefixWord, tailWord_2569156, baseEnd_2569156] using wordTrace_append hprefix tailTrace_2569156
  have hstable : (prefixWord ++ tailWord_2569156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569156).length < 2 ^ (prefixWord ++ tailWord_2569156).sum := by decide
  have hdescent : baseEnd_2569156 < baseStart_2569156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569185 : List Nat := [1, 2, 3, 1, 2, 1, 1, 5, 1, 6]
def baseStart_2569185 : Nat := 118140960795 + 2569185 * 2 ^ 59
def prefixEnd_2569185 : Nat := 4983230072969 + 3 ^ 40 * 2569185 * 2
def baseEnd_2569185 : Nat := 439742265107211928524013

theorem tailTrace_2569185 : CollatzResearch.WordTrace tailWord_2569185 prefixEnd_2569185 439742265107211928524013 := by
  unfold tailWord_2569185
  simp only [CollatzResearch.WordTrace]
  refine ⟨93705875197289001709901009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62470583464859334473267339 93705875197289001709901009)
  ·
    refine ⟨70279406397966751282425757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93705875197289001709901009 70279406397966751282425757)
    ·
      refine ⟨26354777399237531730909659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70279406397966751282425757 26354777399237531730909659)
      ·
        refine ⟨39532166098856297596364489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26354777399237531730909659 39532166098856297596364489)
        ·
          refine ⟨29649124574142223197273367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39532166098856297596364489 29649124574142223197273367)
          ·
            refine ⟨44473686861213334795910051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29649124574142223197273367 44473686861213334795910051)
            ·
              refine ⟨66710530291820002193865077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44473686861213334795910051 66710530291820002193865077)
              ·
                refine ⟨6254112214858125205674851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66710530291820002193865077 6254112214858125205674851)
                ·
                  refine ⟨9381168322287187808512277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6254112214858125205674851 9381168322287187808512277)
                  ·
                    refine ⟨439742265107211928524013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9381168322287187808512277 439742265107211928524013)
                    ·
                      rfl

theorem cell23_2569185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_2569185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569185 prefixEnd_2569185 := by exact prefixLift 2569185
  have htrace : WordTrace (prefixWord ++ tailWord_2569185) baseStart_2569185 baseEnd_2569185 := by
    simpa [prefixWord, tailWord_2569185, baseEnd_2569185] using wordTrace_append hprefix tailTrace_2569185
  have hstable : (prefixWord ++ tailWord_2569185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569185).length < 2 ^ (prefixWord ++ tailWord_2569185).sum := by decide
  have hdescent : baseEnd_2569185 < baseStart_2569185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569189 : List Nat := [1, 3, 1, 6, 1, 1, 1, 1, 3, 5]
def baseStart_2569189 : Nat := 118140960795 + 2569189 * 2 ^ 59
def prefixEnd_2569189 : Nat := 4983230072969 + 3 ^ 40 * 2569189 * 2
def baseEnd_2569189 : Nat := 439742949748084589974007

theorem tailTrace_2569189 : CollatzResearch.WordTrace tailWord_2569189 prefixEnd_2569189 439742949748084589974007 := by
  unfold tailWord_2569189
  simp only [CollatzResearch.WordTrace]
  refine ⟨93706021089274510393046621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62470680726183006928697747 93706021089274510393046621)
  ·
    refine ⟨35139757908477941397392483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93706021089274510393046621 35139757908477941397392483)
    ·
      refine ⟨52709636862716912096088725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35139757908477941397392483 52709636862716912096088725)
      ·
        refine ⟨2470764227939855254504159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 52709636862716912096088725 2470764227939855254504159)
        ·
          refine ⟨3706146341909782881756239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2470764227939855254504159 3706146341909782881756239)
          ·
            refine ⟨5559219512864674322634359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3706146341909782881756239 5559219512864674322634359)
            ·
              refine ⟨8338829269297011483951539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5559219512864674322634359 8338829269297011483951539)
              ·
                refine ⟨12508243903945517225927309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8338829269297011483951539 12508243903945517225927309)
                ·
                  refine ⟨4690591463979568959722741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12508243903945517225927309 4690591463979568959722741)
                  ·
                    refine ⟨439742949748084589974007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4690591463979568959722741 439742949748084589974007)
                    ·
                      rfl

theorem cell23_2569189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 5].length) (baseStart_2569189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569189 prefixEnd_2569189 := by exact prefixLift 2569189
  have htrace : WordTrace (prefixWord ++ tailWord_2569189) baseStart_2569189 baseEnd_2569189 := by
    simpa [prefixWord, tailWord_2569189, baseEnd_2569189] using wordTrace_append hprefix tailTrace_2569189
  have hstable : (prefixWord ++ tailWord_2569189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569189).length < 2 ^ (prefixWord ++ tailWord_2569189).sum := by decide
  have hdescent : baseEnd_2569189 < baseStart_2569189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569192 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 2, 6, 2]
def baseStart_2569192 : Nat := 118140960795 + 2569192 * 2 ^ 59
def prefixEnd_2569192 : Nat := 4983230072969 + 3 ^ 40 * 2569192 * 2
def baseEnd_2569192 : Nat := 1319230389686217258184507

theorem tailTrace_2569192 : CollatzResearch.WordTrace tailWord_2569192 prefixEnd_2569192 1319230389686217258184507 := by
  unfold tailWord_2569192
  simp only [CollatzResearch.WordTrace]
  refine ⟨46853065254131820952702915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62470753672175761270270553 46853065254131820952702915)
  ·
    refine ⟨70279597881197731429054373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46853065254131820952702915 70279597881197731429054373)
    ·
      refine ⟨13177424602724574642947695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70279597881197731429054373 13177424602724574642947695)
      ·
        refine ⟨19766136904086861964421543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13177424602724574642947695 19766136904086861964421543)
        ·
          refine ⟨29649205356130292946632315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19766136904086861964421543 29649205356130292946632315)
          ·
            refine ⟨44473808034195439419948473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29649205356130292946632315 44473808034195439419948473)
            ·
              refine ⟨33355356025646579564961355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44473808034195439419948473 33355356025646579564961355)
              ·
                refine ⟨50033034038469869347442033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33355356025646579564961355 50033034038469869347442033)
                ·
                  refine ⟨37524775528852402010581525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50033034038469869347442033 37524775528852402010581525)
                  ·
                    refine ⟨1758973852914956344246009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37524775528852402010581525 1758973852914956344246009)
                    ·
                      refine ⟨1319230389686217258184507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1758973852914956344246009 1319230389686217258184507)
                      ·
                        rfl

theorem cell23_2569192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_2569192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569192 prefixEnd_2569192 := by exact prefixLift 2569192
  have htrace : WordTrace (prefixWord ++ tailWord_2569192) baseStart_2569192 baseEnd_2569192 := by
    simpa [prefixWord, tailWord_2569192, baseEnd_2569192] using wordTrace_append hprefix tailTrace_2569192
  have hstable : (prefixWord ++ tailWord_2569192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569192).length < 2 ^ (prefixWord ++ tailWord_2569192).sum := by decide
  have hdescent : baseEnd_2569192 < baseStart_2569192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569206 : List Nat := [5, 1, 1, 1, 3, 2, 3, 1, 1, 5]
def baseStart_2569206 : Nat := 118140960795 + 2569206 * 2 ^ 59
def prefixEnd_2569206 : Nat := 4983230072969 + 3 ^ 40 * 2569206 * 2
def baseEnd_2569206 : Nat := 439745859471793401136481

theorem tailTrace_2569206 : CollatzResearch.WordTrace tailWord_2569206 prefixEnd_2569206 439745859471793401136481 := by
  unfold tailWord_2569206
  simp only [CollatzResearch.WordTrace]
  refine ⟨5856665070638307643525967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62471094086808614864276981 5856665070638307643525967)
  ·
    refine ⟨8784997605957461465288951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5856665070638307643525967 8784997605957461465288951)
    ·
      refine ⟨13177496408936192197933427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8784997605957461465288951 13177496408936192197933427)
      ·
        refine ⟨19766244613404288296900141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13177496408936192197933427 19766244613404288296900141)
        ·
          refine ⟨7412341730026608111337553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19766244613404288296900141 7412341730026608111337553)
          ·
            refine ⟨5559256297519956083503165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7412341730026608111337553 5559256297519956083503165)
            ·
              refine ⟨2084721111569983531313687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5559256297519956083503165 2084721111569983531313687)
              ·
                refine ⟨3127081667354975296970531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2084721111569983531313687 3127081667354975296970531)
                ·
                  refine ⟨4690622501032462945455797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3127081667354975296970531 4690622501032462945455797)
                  ·
                    refine ⟨439745859471793401136481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4690622501032462945455797 439745859471793401136481)
                    ·
                      rfl

theorem cell23_2569206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_2569206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569206 prefixEnd_2569206 := by exact prefixLift 2569206
  have htrace : WordTrace (prefixWord ++ tailWord_2569206) baseStart_2569206 baseEnd_2569206 := by
    simpa [prefixWord, tailWord_2569206, baseEnd_2569206] using wordTrace_append hprefix tailTrace_2569206
  have hstable : (prefixWord ++ tailWord_2569206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569206).length < 2 ^ (prefixWord ++ tailWord_2569206).sum := by decide
  have hdescent : baseEnd_2569206 < baseStart_2569206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569209 : List Nat := [1, 2, 1, 3, 1, 3, 5, 1, 1, 1, 4]
def baseStart_2569209 : Nat := 118140960795 + 2569209 * 2 ^ 59
def prefixEnd_2569209 : Nat := 4983230072969 + 3 ^ 40 * 2569209 * 2
def baseEnd_2569209 : Nat := 1319239118857343691671929

theorem tailTrace_2569209 : CollatzResearch.WordTrace tailWord_2569209 prefixEnd_2569209 1319239118857343691671929 := by
  unfold tailWord_2569209
  simp only [CollatzResearch.WordTrace]
  refine ⟨93706750549202053808774681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62471167032801369205849787 93706750549202053808774681)
  ·
    refine ⟨70280062911901540356581011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93706750549202053808774681 70280062911901540356581011)
    ·
      refine ⟨105420094367852310534871517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70280062911901540356581011 105420094367852310534871517)
      ·
        refine ⟨39532535387944616450576819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105420094367852310534871517 39532535387944616450576819)
        ·
          refine ⟨59298803081916924675865229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39532535387944616450576819 59298803081916924675865229)
          ·
            refine ⟨22237051155718846753449461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59298803081916924675865229 22237051155718846753449461)
            ·
              refine ⟨2084723545848641883135887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22237051155718846753449461 2084723545848641883135887)
              ·
                refine ⟨3127085318772962824703831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2084723545848641883135887 3127085318772962824703831)
                ·
                  refine ⟨4690627978159444237055747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3127085318772962824703831 4690627978159444237055747)
                  ·
                    refine ⟨7035941967239166355583621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4690627978159444237055747 7035941967239166355583621)
                    ·
                      refine ⟨1319239118857343691671929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7035941967239166355583621 1319239118857343691671929)
                      ·
                        rfl

theorem cell23_2569209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 1, 1, 4].length) (baseStart_2569209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569209 prefixEnd_2569209 := by exact prefixLift 2569209
  have htrace : WordTrace (prefixWord ++ tailWord_2569209) baseStart_2569209 baseEnd_2569209 := by
    simpa [prefixWord, tailWord_2569209, baseEnd_2569209] using wordTrace_append hprefix tailTrace_2569209
  have hstable : (prefixWord ++ tailWord_2569209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569209).length < 2 ^ (prefixWord ++ tailWord_2569209).sum := by decide
  have hdescent : baseEnd_2569209 < baseStart_2569209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569212 : List Nat := [2, 2, 2, 1, 2, 3, 3, 1, 1, 1, 5]
def baseStart_2569212 : Nat := 118140960795 + 2569212 * 2 ^ 59
def prefixEnd_2569212 : Nat := 4983230072969 + 3 ^ 40 * 2569212 * 2
def baseEnd_2569212 : Nat := 1319240659299307179934415

theorem tailTrace_2569212 : CollatzResearch.WordTrace tailWord_2569212 prefixEnd_2569212 1319240659299307179934415 := by
  unfold tailWord_2569212
  simp only [CollatzResearch.WordTrace]
  refine ⟨46853429984095592660566945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62471239978794123547422593 46853429984095592660566945)
  ·
    refine ⟨35140072488071694495425209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46853429984095592660566945 35140072488071694495425209)
    ·
      refine ⟨26355054366053770871568907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35140072488071694495425209 26355054366053770871568907)
      ·
        refine ⟨39532581549080656307353361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26355054366053770871568907 39532581549080656307353361)
        ·
          refine ⟨29649436161810492230515021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39532581549080656307353361 29649436161810492230515021)
          ·
            refine ⟨11118538560678934586443133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29649436161810492230515021 11118538560678934586443133)
            ·
              refine ⟨4169451960254600469916175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11118538560678934586443133 4169451960254600469916175)
              ·
                refine ⟨6254177940381900704874263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4169451960254600469916175 6254177940381900704874263)
                ·
                  refine ⟨9381266910572851057311395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6254177940381900704874263 9381266910572851057311395)
                  ·
                    refine ⟨14071900365859276585967093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9381266910572851057311395 14071900365859276585967093)
                    ·
                      refine ⟨1319240659299307179934415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14071900365859276585967093 1319240659299307179934415)
                      ·
                        rfl

theorem cell23_2569212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_2569212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569212 prefixEnd_2569212 := by exact prefixLift 2569212
  have htrace : WordTrace (prefixWord ++ tailWord_2569212) baseStart_2569212 baseEnd_2569212 := by
    simpa [prefixWord, tailWord_2569212, baseEnd_2569212] using wordTrace_append hprefix tailTrace_2569212
  have hstable : (prefixWord ++ tailWord_2569212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569212).length < 2 ^ (prefixWord ++ tailWord_2569212).sum := by decide
  have hdescent : baseEnd_2569212 < baseStart_2569212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569239 : List Nat := [1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 4]
def baseStart_2569239 : Nat := 118140960795 + 2569239 * 2 ^ 59
def prefixEnd_2569239 : Nat := 4983230072969 + 3 ^ 40 * 2569239 * 2
def baseEnd_2569239 : Nat := 1319254523276978574296791

theorem tailTrace_2569239 : CollatzResearch.WordTrace tailWord_2569239 prefixEnd_2569239 1319254523276978574296791 := by
  unfold tailWord_2569239
  simp only [CollatzResearch.WordTrace]
  refine ⟨93707844739093368932366771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62471896492728912621577847 93707844739093368932366771)
  ·
    refine ⟨140561767108640053398550157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93707844739093368932366771 140561767108640053398550157)
    ·
      refine ⟨52710662665740020024456309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140561767108640053398550157 52710662665740020024456309)
      ·
        refine ⟨4941624624913126877292779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52710662665740020024456309 4941624624913126877292779)
        ·
          refine ⟨7412436937369690315939169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4941624624913126877292779 7412436937369690315939169)
          ·
            refine ⟨5559327703027267736954377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7412436937369690315939169 5559327703027267736954377)
            ·
              refine ⟨4169495777270450802715783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5559327703027267736954377 4169495777270450802715783)
              ·
                refine ⟨6254243665905676204073675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4169495777270450802715783 6254243665905676204073675)
                ·
                  refine ⟨9381365498858514306110513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6254243665905676204073675 9381365498858514306110513)
                  ·
                    refine ⟨7036024124143885729582885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9381365498858514306110513 7036024124143885729582885)
                    ·
                      refine ⟨1319254523276978574296791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7036024124143885729582885 1319254523276978574296791)
                      ·
                        rfl

theorem cell23_2569239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_2569239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569239 prefixEnd_2569239 := by exact prefixLift 2569239
  have htrace : WordTrace (prefixWord ++ tailWord_2569239) baseStart_2569239 baseEnd_2569239 := by
    simpa [prefixWord, tailWord_2569239, baseEnd_2569239] using wordTrace_append hprefix tailTrace_2569239
  have hstable : (prefixWord ++ tailWord_2569239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569239).length < 2 ^ (prefixWord ++ tailWord_2569239).sum := by decide
  have hdescent : baseEnd_2569239 < baseStart_2569239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569276 : List Nat := [2, 2, 2, 2, 2, 2, 3, 2, 2, 1, 3]
def baseStart_2569276 : Nat := 118140960795 + 2569276 * 2 ^ 59
def prefixEnd_2569276 : Nat := 4983230072969 + 3 ^ 40 * 2569276 * 2
def baseEnd_2569276 : Nat := 1319273522061194929534121

theorem tailTrace_2569276 : CollatzResearch.WordTrace tailWord_2569276 prefixEnd_2569276 1319273522061194929534121 := by
  unfold tailWord_2569276
  simp only [CollatzResearch.WordTrace]
  refine ⟨46854597119979662125731841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62472796159972882834309121 46854597119979662125731841)
  ·
    refine ⟨35140947839984746594298881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46854597119979662125731841 35140947839984746594298881)
    ·
      refine ⟨26355710879988559945724161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35140947839984746594298881 26355710879988559945724161)
      ·
        refine ⟨19766783159991419959293121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26355710879988559945724161 19766783159991419959293121)
        ·
          refine ⟨14825087369993564969469841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19766783159991419959293121 14825087369993564969469841)
          ·
            refine ⟨11118815527495173727102381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14825087369993564969469841 11118815527495173727102381)
            ·
              refine ⟨4169555822810690147663393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11118815527495173727102381 4169555822810690147663393)
              ·
                refine ⟨3127166867108017610747545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4169555822810690147663393 3127166867108017610747545)
                ·
                  refine ⟨2345375150331013208060659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3127166867108017610747545 2345375150331013208060659)
                  ·
                    refine ⟨3518062725496519812090989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2345375150331013208060659 3518062725496519812090989)
                    ·
                      refine ⟨1319273522061194929534121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3518062725496519812090989 1319273522061194929534121)
                      ·
                        rfl

theorem cell23_2569276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_2569276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569276 prefixEnd_2569276 := by exact prefixLift 2569276
  have htrace : WordTrace (prefixWord ++ tailWord_2569276) baseStart_2569276 baseEnd_2569276 := by
    simpa [prefixWord, tailWord_2569276, baseEnd_2569276] using wordTrace_append hprefix tailTrace_2569276
  have hstable : (prefixWord ++ tailWord_2569276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569276).length < 2 ^ (prefixWord ++ tailWord_2569276).sum := by decide
  have hdescent : baseEnd_2569276 < baseStart_2569276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569299 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 6, 2, 2]
def baseStart_2569299 : Nat := 118140960795 + 2569299 * 2 ^ 59
def prefixEnd_2569299 : Nat := 4983230072969 + 3 ^ 40 * 2569299 * 2
def baseEnd_2569299 : Nat := 1319285332116248339546515

theorem tailTrace_2569299 : CollatzResearch.WordTrace tailWord_2569299 prefixEnd_2569299 1319285332116248339546515 := by
  unfold tailWord_2569299
  simp only [CollatzResearch.WordTrace]
  refine ⟨93710033118875999179550951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62473355412583999453033967 93710033118875999179550951)
  ·
    refine ⟨140565049678313998769326427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93710033118875999179550951 140565049678313998769326427)
    ·
      refine ⟨210847574517470998153989641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140565049678313998769326427 210847574517470998153989641)
      ·
        refine ⟨158135680888103248615492231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210847574517470998153989641 158135680888103248615492231)
        ·
          refine ⟨237203521332154872923238347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158135680888103248615492231 237203521332154872923238347)
          ·
            refine ⟨355805281998232309384857521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237203521332154872923238347 355805281998232309384857521)
            ·
              refine ⟨266853961498674232038643141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 355805281998232309384857521 266853961498674232038643141)
              ·
                refine ⟨50035117781001418507245589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 266853961498674232038643141 50035117781001418507245589)
                ·
                  refine ⟨2345396145984441492527137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50035117781001418507245589 2345396145984441492527137)
                  ·
                    refine ⟨1759047109488331119395353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2345396145984441492527137 1759047109488331119395353)
                    ·
                      refine ⟨1319285332116248339546515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1759047109488331119395353 1319285332116248339546515)
                      ·
                        rfl

theorem cell23_2569299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 6, 2, 2].length) (baseStart_2569299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569299 prefixEnd_2569299 := by exact prefixLift 2569299
  have htrace : WordTrace (prefixWord ++ tailWord_2569299) baseStart_2569299 baseEnd_2569299 := by
    simpa [prefixWord, tailWord_2569299, baseEnd_2569299] using wordTrace_append hprefix tailTrace_2569299
  have hstable : (prefixWord ++ tailWord_2569299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569299).length < 2 ^ (prefixWord ++ tailWord_2569299).sum := by decide
  have hdescent : baseEnd_2569299 < baseStart_2569299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569305 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 9]
def baseStart_2569305 : Nat := 118140960795 + 2569305 * 2 ^ 59
def prefixEnd_2569305 : Nat := 4983230072969 + 3 ^ 40 * 2569305 * 2
def baseEnd_2569305 : Nat := 146587601444463924007943

theorem tailTrace_2569305 : CollatzResearch.WordTrace tailWord_2569305 prefixEnd_2569305 146587601444463924007943 := by
  unfold tailWord_2569305
  simp only [CollatzResearch.WordTrace]
  refine ⟨93710251956854262204269369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62473501304569508136179579 93710251956854262204269369)
  ·
    refine ⟨70282688967640696653202027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93710251956854262204269369 70282688967640696653202027)
    ·
      refine ⟨105424033451461044979803041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70282688967640696653202027 105424033451461044979803041)
      ·
        refine ⟨79068025088595783734852281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105424033451461044979803041 79068025088595783734852281)
        ·
          refine ⟨59301018816446837801139211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79068025088595783734852281 59301018816446837801139211)
          ·
            refine ⟨88951528224670256701708817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59301018816446837801139211 88951528224670256701708817)
            ·
              refine ⟨66713646168502692526281613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88951528224670256701708817 66713646168502692526281613)
              ·
                refine ⟨25017617313188509697355605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66713646168502692526281613 25017617313188509697355605)
                ·
                  refine ⟨146587601444463924007943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25017617313188509697355605 146587601444463924007943)
                  ·
                    rfl

theorem cell23_2569305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 9].length) (baseStart_2569305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569305 prefixEnd_2569305 := by exact prefixLift 2569305
  have htrace : WordTrace (prefixWord ++ tailWord_2569305) baseStart_2569305 baseEnd_2569305 := by
    simpa [prefixWord, tailWord_2569305, baseEnd_2569305] using wordTrace_append hprefix tailTrace_2569305
  have hstable : (prefixWord ++ tailWord_2569305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569305).length < 2 ^ (prefixWord ++ tailWord_2569305).sum := by decide
  have hdescent : baseEnd_2569305 < baseStart_2569305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569386 : List Nat := [3, 1, 5, 1, 1, 1, 2, 2, 2, 5]
def baseStart_2569386 : Nat := 118140960795 + 2569386 * 2 ^ 59
def prefixEnd_2569386 : Nat := 4983230072969 + 3 ^ 40 * 2569386 * 2
def baseEnd_2569386 : Nat := 439776668311063166386205

theorem tailTrace_2569386 : CollatzResearch.WordTrace tailWord_2569386 prefixEnd_2569386 439776668311063166386205 := by
  unfold tailWord_2569386
  simp only [CollatzResearch.WordTrace]
  refine ⟨23428301567390203259492003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62475470846373875358645341 23428301567390203259492003)
  ·
    refine ⟨35142452351085304889238005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23428301567390203259492003 35142452351085304889238005)
    ·
      refine ⟨3294604907914247333366063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35142452351085304889238005 3294604907914247333366063)
      ·
        refine ⟨4941907361871371000049095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3294604907914247333366063 4941907361871371000049095)
        ·
          refine ⟨7412861042807056500073643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4941907361871371000049095 7412861042807056500073643)
          ·
            refine ⟨11119291564210584750110465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7412861042807056500073643 11119291564210584750110465)
            ·
              refine ⟨8339468673157938562582849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11119291564210584750110465 8339468673157938562582849)
              ·
                refine ⟨6254601504868453921937137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8339468673157938562582849 6254601504868453921937137)
                ·
                  refine ⟨4690951128651340441452853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6254601504868453921937137 4690951128651340441452853)
                  ·
                    refine ⟨439776668311063166386205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4690951128651340441452853 439776668311063166386205)
                    ·
                      rfl

theorem cell23_2569386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_2569386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569386 prefixEnd_2569386 := by exact prefixLift 2569386
  have htrace : WordTrace (prefixWord ++ tailWord_2569386) baseStart_2569386 baseEnd_2569386 := by
    simpa [prefixWord, tailWord_2569386, baseEnd_2569386] using wordTrace_append hprefix tailTrace_2569386
  have hstable : (prefixWord ++ tailWord_2569386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569386).length < 2 ^ (prefixWord ++ tailWord_2569386).sum := by decide
  have hdescent : baseEnd_2569386 < baseStart_2569386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569399 : List Nat := [1, 1, 3, 1, 4, 1, 2, 3, 3, 4]
def baseStart_2569399 : Nat := 118140960795 + 2569399 * 2 ^ 59
def prefixEnd_2569399 : Nat := 4983230072969 + 3 ^ 40 * 2569399 * 2
def baseEnd_2569399 : Nat := 439778893393899316098685

theorem tailTrace_2569399 : CollatzResearch.WordTrace tailWord_2569399 prefixEnd_2569399 439778893393899316098685 := by
  unfold tailWord_2569399
  simp only [CollatzResearch.WordTrace]
  refine ⟨93713680418513716258191251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62475786945675810838794167 93713680418513716258191251)
  ·
    refine ⟨140570520627770574387286877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93713680418513716258191251 140570520627770574387286877)
    ·
      refine ⟨52713945235413965395232579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140570520627770574387286877 52713945235413965395232579)
      ·
        refine ⟨79070917853120948092848869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52713945235413965395232579 79070917853120948092848869)
        ·
          refine ⟨14825797097460177767409163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79070917853120948092848869 14825797097460177767409163)
          ·
            refine ⟨22238695646190266651113745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14825797097460177767409163 22238695646190266651113745)
            ·
              refine ⟨16679021734642699988335309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22238695646190266651113745 16679021734642699988335309)
              ·
                refine ⟨6254633150491012495625741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16679021734642699988335309 6254633150491012495625741)
                ·
                  refine ⟨2345487431434129685859653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6254633150491012495625741 2345487431434129685859653)
                  ·
                    refine ⟨439778893393899316098685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2345487431434129685859653 439778893393899316098685)
                    ·
                      rfl

theorem cell23_2569399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 3, 4].length) (baseStart_2569399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569399 prefixEnd_2569399 := by exact prefixLift 2569399
  have htrace : WordTrace (prefixWord ++ tailWord_2569399) baseStart_2569399 baseEnd_2569399 := by
    simpa [prefixWord, tailWord_2569399, baseEnd_2569399] using wordTrace_append hprefix tailTrace_2569399
  have hstable : (prefixWord ++ tailWord_2569399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569399).length < 2 ^ (prefixWord ++ tailWord_2569399).sum := by decide
  have hdescent : baseEnd_2569399 < baseStart_2569399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569402 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 2, 4, 4]
def baseStart_2569402 : Nat := 118140960795 + 2569402 * 2 ^ 59
def prefixEnd_2569402 : Nat := 4983230072969 + 3 ^ 40 * 2569402 * 2
def baseEnd_2569402 : Nat := 1319338220623661436558541

theorem tailTrace_2569402 : CollatzResearch.WordTrace tailWord_2569402 prefixEnd_2569402 1319338220623661436558541 := by
  unfold tailWord_2569402
  simp only [CollatzResearch.WordTrace]
  refine ⟨23428447459375711942637615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62475859891668565180366973 23428447459375711942637615)
  ·
    refine ⟨35142671189063567913956423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23428447459375711942637615 35142671189063567913956423)
    ·
      refine ⟨52714006783595351870934635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35142671189063567913956423 52714006783595351870934635)
      ·
        refine ⟨79071010175393027806401953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52714006783595351870934635 79071010175393027806401953)
        ·
          refine ⟨59303257631544770854801465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79071010175393027806401953 59303257631544770854801465)
          ·
            refine ⟨44477443223658578141101099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59303257631544770854801465 44477443223658578141101099)
            ·
              refine ⟨66716164835487867211651649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44477443223658578141101099 66716164835487867211651649)
              ·
                refine ⟨50037123626615900408738737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66716164835487867211651649 50037123626615900408738737)
                ·
                  refine ⟨37527842719961925306554053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50037123626615900408738737 37527842719961925306554053)
                  ·
                    refine ⟨7036470509992860994978885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37527842719961925306554053 7036470509992860994978885)
                    ·
                      refine ⟨1319338220623661436558541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7036470509992860994978885 1319338220623661436558541)
                      ·
                        rfl

theorem cell23_2569402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_2569402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569402 prefixEnd_2569402 := by exact prefixLift 2569402
  have htrace : WordTrace (prefixWord ++ tailWord_2569402) baseStart_2569402 baseEnd_2569402 := by
    simpa [prefixWord, tailWord_2569402, baseEnd_2569402] using wordTrace_append hprefix tailTrace_2569402
  have hstable : (prefixWord ++ tailWord_2569402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569402).length < 2 ^ (prefixWord ++ tailWord_2569402).sum := by decide
  have hdescent : baseEnd_2569402 < baseStart_2569402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569406 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2]
def baseStart_2569406 : Nat := 118140960795 + 2569406 * 2 ^ 59
def prefixEnd_2569406 : Nat := 4983230072969 + 3 ^ 40 * 2569406 * 2
def baseEnd_2569406 : Nat := 1319340274546279420908523

theorem tailTrace_2569406 : CollatzResearch.WordTrace tailWord_2569406 prefixEnd_2569406 1319340274546279420908523 := by
  unfold tailWord_2569406
  simp only [CollatzResearch.WordTrace]
  refine ⟨11714241966186044556712009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62475957152992237635797381 11714241966186044556712009)
  ·
    refine ⟨8785681474639533417534007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11714241966186044556712009 8785681474639533417534007)
    ·
      refine ⟨13178522211959300126301011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8785681474639533417534007 13178522211959300126301011)
      ·
        refine ⟨19767783317938950189451517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13178522211959300126301011 19767783317938950189451517)
        ·
          refine ⟨7412918744227106321044319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19767783317938950189451517 7412918744227106321044319)
          ·
            refine ⟨11119378116340659481566479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7412918744227106321044319 11119378116340659481566479)
            ·
              refine ⟨16679067174510989222349719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11119378116340659481566479 16679067174510989222349719)
              ·
                refine ⟨25018600761766483833524579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16679067174510989222349719 25018600761766483833524579)
                ·
                  refine ⟨37527901142649725750286869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25018600761766483833524579 37527901142649725750286869)
                  ·
                    refine ⟨1759120366061705894544697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37527901142649725750286869 1759120366061705894544697)
                    ·
                      refine ⟨1319340274546279420908523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1759120366061705894544697 1319340274546279420908523)
                      ·
                        rfl

theorem cell23_2569406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_2569406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569406 prefixEnd_2569406 := by exact prefixLift 2569406
  have htrace : WordTrace (prefixWord ++ tailWord_2569406) baseStart_2569406 baseEnd_2569406 := by
    simpa [prefixWord, tailWord_2569406, baseEnd_2569406] using wordTrace_append hprefix tailTrace_2569406
  have hstable : (prefixWord ++ tailWord_2569406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569406).length < 2 ^ (prefixWord ++ tailWord_2569406).sum := by decide
  have hdescent : baseEnd_2569406 < baseStart_2569406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569449 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 5, 5, 2]
def baseStart_2569449 : Nat := 118140960795 + 2569449 * 2 ^ 59
def prefixEnd_2569449 : Nat := 4983230072969 + 3 ^ 40 * 2569449 * 2
def baseEnd_2569449 : Nat := 1319362354214422752670825

theorem tailTrace_2569449 : CollatzResearch.WordTrace tailWord_2569449 prefixEnd_2569449 1319362354214422752670825 := by
  unfold tailWord_2569449
  simp only [CollatzResearch.WordTrace]
  refine ⟨93715504068332574797511401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62477002712221716531674267 93715504068332574797511401)
  ·
    refine ⟨70286628051249431098133551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93715504068332574797511401 70286628051249431098133551)
    ·
      refine ⟨105429942076874146647200327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70286628051249431098133551 105429942076874146647200327)
      ·
        refine ⟨158144913115311219970800491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105429942076874146647200327 158144913115311219970800491)
        ·
          refine ⟨237217369672966829956200737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158144913115311219970800491 237217369672966829956200737)
          ·
            refine ⟨177913027254725122467150553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237217369672966829956200737 177913027254725122467150553)
            ·
              refine ⟨133434770441043841850362915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177913027254725122467150553 133434770441043841850362915)
              ·
                refine ⟨200152155661565762775544373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133434770441043841850362915 200152155661565762775544373)
                ·
                  refine ⟨18764264593271790260207285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 200152155661565762775544373 18764264593271790260207285)
                  ·
                    refine ⟨1759149805619230336894433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18764264593271790260207285 1759149805619230336894433)
                    ·
                      refine ⟨1319362354214422752670825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1759149805619230336894433 1319362354214422752670825)
                      ·
                        rfl

theorem cell23_2569449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 5, 2].length) (baseStart_2569449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569449 prefixEnd_2569449 := by exact prefixLift 2569449
  have htrace : WordTrace (prefixWord ++ tailWord_2569449) baseStart_2569449 baseEnd_2569449 := by
    simpa [prefixWord, tailWord_2569449, baseEnd_2569449] using wordTrace_append hprefix tailTrace_2569449
  have hstable : (prefixWord ++ tailWord_2569449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569449).length < 2 ^ (prefixWord ++ tailWord_2569449).sum := by decide
  have hdescent : baseEnd_2569449 < baseStart_2569449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569476 : List Nat := [2, 3, 2, 2, 2, 1, 1, 4, 1, 5]
def baseStart_2569476 : Nat := 118140960795 + 2569476 * 2 ^ 59
def prefixEnd_2569476 : Nat := 4983230072969 + 3 ^ 40 * 2569476 * 2
def baseEnd_2569476 : Nat := 439792072730698049011067

theorem tailTrace_2569476 : CollatzResearch.WordTrace tailWord_2569476 prefixEnd_2569476 439792072730698049011067 := by
  unfold tailWord_2569476
  simp only [CollatzResearch.WordTrace]
  refine ⟨46858244419617379204372141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62477659226156505605829521 46858244419617379204372141)
  ·
    refine ⟨17571841657356517201639553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46858244419617379204372141 17571841657356517201639553)
    ·
      refine ⟨13178881243017387901229665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17571841657356517201639553 13178881243017387901229665)
      ·
        refine ⟨9884160932263040925922249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13178881243017387901229665 9884160932263040925922249)
        ·
          refine ⟨7413120699197280694441687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9884160932263040925922249 7413120699197280694441687)
          ·
            refine ⟨11119681048795921041662531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7413120699197280694441687 11119681048795921041662531)
            ·
              refine ⟨16679521573193881562493797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11119681048795921041662531 16679521573193881562493797)
              ·
                refine ⟨3127410294973852792967587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16679521573193881562493797 3127410294973852792967587)
                ·
                  refine ⟨4691115442460779189451381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3127410294973852792967587 4691115442460779189451381)
                  ·
                    refine ⟨439792072730698049011067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4691115442460779189451381 439792072730698049011067)
                    ·
                      rfl

theorem cell23_2569476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_2569476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569476 prefixEnd_2569476 := by exact prefixLift 2569476
  have htrace : WordTrace (prefixWord ++ tailWord_2569476) baseStart_2569476 baseEnd_2569476 := by
    simpa [prefixWord, tailWord_2569476, baseEnd_2569476] using wordTrace_append hprefix tailTrace_2569476
  have hstable : (prefixWord ++ tailWord_2569476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569476).length < 2 ^ (prefixWord ++ tailWord_2569476).sum := by decide
  have hdescent : baseEnd_2569476 < baseStart_2569476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569489 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 6, 4]
def baseStart_2569489 : Nat := 118140960795 + 2569489 * 2 ^ 59
def prefixEnd_2569489 : Nat := 4983230072969 + 3 ^ 40 * 2569489 * 2
def baseEnd_2569489 : Nat := 439794297813534198723547

theorem tailTrace_2569489 : CollatzResearch.WordTrace tailWord_2569489 prefixEnd_2569489 439794297813534198723547 := by
  unfold tailWord_2569489
  simp only [CollatzResearch.WordTrace]
  refine ⟨93716962988187661628967521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62477975325458441085978347 93716962988187661628967521)
  ·
    refine ⟨70287722241140746221725641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93716962988187661628967521 70287722241140746221725641)
    ·
      refine ⟨52715791680855559666294231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70287722241140746221725641 52715791680855559666294231)
      ·
        refine ⟨79073687521283339499441347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52715791680855559666294231 79073687521283339499441347)
        ·
          refine ⟨118610531281925009249162021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79073687521283339499441347 118610531281925009249162021)
          ·
            refine ⟨22239474615360939234217879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118610531281925009249162021 22239474615360939234217879)
            ·
              refine ⟨33359211923041408851326819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22239474615360939234217879 33359211923041408851326819)
              ·
                refine ⟨50038817884562113276990229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33359211923041408851326819 50038817884562113276990229)
                ·
                  refine ⟨2345569588338849059858917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50038817884562113276990229 2345569588338849059858917)
                  ·
                    refine ⟨439794297813534198723547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2345569588338849059858917 439794297813534198723547)
                    ·
                      rfl

theorem cell23_2569489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 6, 4].length) (baseStart_2569489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569489 prefixEnd_2569489 := by exact prefixLift 2569489
  have htrace : WordTrace (prefixWord ++ tailWord_2569489) baseStart_2569489 baseEnd_2569489 := by
    simpa [prefixWord, tailWord_2569489, baseEnd_2569489] using wordTrace_append hprefix tailTrace_2569489
  have hstable : (prefixWord ++ tailWord_2569489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569489).length < 2 ^ (prefixWord ++ tailWord_2569489).sum := by decide
  have hdescent : baseEnd_2569489 < baseStart_2569489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569496 : List Nat := [2, 1, 2, 3, 1, 3, 2, 3, 1, 1, 4]
def baseStart_2569496 : Nat := 118140960795 + 2569496 * 2 ^ 59
def prefixEnd_2569496 : Nat := 4983230072969 + 3 ^ 40 * 2569496 * 2
def baseEnd_2569496 : Nat := 1319386487805184068783109

theorem tailTrace_2569496 : CollatzResearch.WordTrace tailWord_2569496 prefixEnd_2569496 1319386487805184068783109 := by
  unfold tailWord_2569496
  simp only [CollatzResearch.WordTrace]
  refine ⟨46858609149581150912236171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62478145532774867882981561 46858609149581150912236171)
  ·
    refine ⟨70287913724371726368354257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46858609149581150912236171 70287913724371726368354257)
    ·
      refine ⟨52715935293278794776265693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70287913724371726368354257 52715935293278794776265693)
      ·
        refine ⟨19768475734979548041099635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52715935293278794776265693 19768475734979548041099635)
        ·
          refine ⟨29652713602469322061649453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19768475734979548041099635 29652713602469322061649453)
          ·
            refine ⟨11119767600925995773118545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29652713602469322061649453 11119767600925995773118545)
            ·
              refine ⟨8339825700694496829838909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11119767600925995773118545 8339825700694496829838909)
              ·
                refine ⟨3127434637760436311189591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8339825700694496829838909 3127434637760436311189591)
                ·
                  refine ⟨4691151956640654466784387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3127434637760436311189591 4691151956640654466784387)
                  ·
                    refine ⟨7036727934960981700176581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4691151956640654466784387 7036727934960981700176581)
                    ·
                      refine ⟨1319386487805184068783109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7036727934960981700176581 1319386487805184068783109)
                      ·
                        rfl

theorem cell23_2569496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_2569496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569496 prefixEnd_2569496 := by exact prefixLift 2569496
  have htrace : WordTrace (prefixWord ++ tailWord_2569496) baseStart_2569496 baseEnd_2569496 := by
    simpa [prefixWord, tailWord_2569496, baseEnd_2569496] using wordTrace_append hprefix tailTrace_2569496
  have hstable : (prefixWord ++ tailWord_2569496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569496).length < 2 ^ (prefixWord ++ tailWord_2569496).sum := by decide
  have hdescent : baseEnd_2569496 < baseStart_2569496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569499 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 5, 2, 3]
def baseStart_2569499 : Nat := 118140960795 + 2569499 * 2 ^ 59
def prefixEnd_2569499 : Nat := 4983230072969 + 3 ^ 40 * 2569499 * 2
def baseEnd_2569499 : Nat := 1319388028247147557045595

theorem tailTrace_2569499 : CollatzResearch.WordTrace tailWord_2569499 prefixEnd_2569499 1319388028247147557045595 := by
  unfold tailWord_2569499
  simp only [CollatzResearch.WordTrace]
  refine ⟨93717327718151433336831551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62478218478767622224554367 93717327718151433336831551)
  ·
    refine ⟨140575991577227150005247327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93717327718151433336831551 140575991577227150005247327)
    ·
      refine ⟨210863987365840725007870991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140575991577227150005247327 210863987365840725007870991)
      ·
        refine ⟨316295981048761087511806487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210863987365840725007870991 316295981048761087511806487)
        ·
          refine ⟨474443971573141631267709731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316295981048761087511806487 474443971573141631267709731)
          ·
            refine ⟨711665957359712446901564597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 474443971573141631267709731 711665957359712446901564597)
            ·
              refine ⟨66718683502473041897021681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 711665957359712446901564597 66718683502473041897021681)
              ·
                refine ⟨50039012626854781422766261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66718683502473041897021681 50039012626854781422766261)
                ·
                  refine ⟨4691157433767635758384337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50039012626854781422766261 4691157433767635758384337)
                  ·
                    refine ⟨3518368075325726818788253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4691157433767635758384337 3518368075325726818788253)
                    ·
                      refine ⟨1319388028247147557045595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3518368075325726818788253 1319388028247147557045595)
                      ·
                        rfl

theorem cell23_2569499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 2, 3].length) (baseStart_2569499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569499 prefixEnd_2569499 := by exact prefixLift 2569499
  have htrace : WordTrace (prefixWord ++ tailWord_2569499) baseStart_2569499 baseEnd_2569499 := by
    simpa [prefixWord, tailWord_2569499, baseEnd_2569499] using wordTrace_append hprefix tailTrace_2569499
  have hstable : (prefixWord ++ tailWord_2569499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569499).length < 2 ^ (prefixWord ++ tailWord_2569499).sum := by decide
  have hdescent : baseEnd_2569499 < baseStart_2569499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569509 : List Nat := [1, 3, 1, 2, 4, 1, 1, 2, 1, 1, 6]
def baseStart_2569509 : Nat := 118140960795 + 2569509 * 2 ^ 59
def prefixEnd_2569509 : Nat := 4983230072969 + 3 ^ 40 * 2569509 * 2
def baseEnd_2569509 : Nat := 1319393163053692517920549

theorem tailTrace_2569509 : CollatzResearch.WordTrace tailWord_2569509 prefixEnd_2569509 1319393163053692517920549 := by
  unfold tailWord_2569509
  simp only [CollatzResearch.WordTrace]
  refine ⟨93717692448115205044695581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62478461632076803363130387 93717692448115205044695581)
  ·
    refine ⟨35144134668043201891760843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93717692448115205044695581 35144134668043201891760843)
    ·
      refine ⟨52716202002064802837641265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35144134668043201891760843 52716202002064802837641265)
      ·
        refine ⟨39537151501548602128230949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52716202002064802837641265 39537151501548602128230949)
        ·
          refine ⟨7413215906540362899043303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39537151501548602128230949 7413215906540362899043303)
          ·
            refine ⟨11119823859810544348564955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7413215906540362899043303 11119823859810544348564955)
            ·
              refine ⟨16679735789715816522847433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11119823859810544348564955 16679735789715816522847433)
              ·
                refine ⟨12509801842286862392135575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16679735789715816522847433 12509801842286862392135575)
                ·
                  refine ⟨18764702763430293588203363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12509801842286862392135575 18764702763430293588203363)
                  ·
                    refine ⟨28147054145145440382305045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18764702763430293588203363 28147054145145440382305045)
                    ·
                      refine ⟨1319393163053692517920549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28147054145145440382305045 1319393163053692517920549)
                      ·
                        rfl

theorem cell23_2569509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_2569509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569509 prefixEnd_2569509 := by exact prefixLift 2569509
  have htrace : WordTrace (prefixWord ++ tailWord_2569509) baseStart_2569509 baseEnd_2569509 := by
    simpa [prefixWord, tailWord_2569509, baseEnd_2569509] using wordTrace_append hprefix tailTrace_2569509
  have hstable : (prefixWord ++ tailWord_2569509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569509).length < 2 ^ (prefixWord ++ tailWord_2569509).sum := by decide
  have hdescent : baseEnd_2569509 < baseStart_2569509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569523 : List Nat := [1, 1, 1, 2, 5, 2, 4, 1, 2, 4]
def baseStart_2569523 : Nat := 118140960795 + 2569523 * 2 ^ 59
def prefixEnd_2569523 : Nat := 4983230072969 + 3 ^ 40 * 2569523 * 2
def baseEnd_2569523 : Nat := 439800117260951821048495

theorem tailTrace_2569523 : CollatzResearch.WordTrace tailWord_2569523 prefixEnd_2569523 439800117260951821048495 := by
  unfold tailWord_2569523
  simp only [CollatzResearch.WordTrace]
  refine ⟨93718203070064485435705223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62478802046709656957136815 93718203070064485435705223)
  ·
    refine ⟨140577304605096728153557835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93718203070064485435705223 140577304605096728153557835)
    ·
      refine ⟨210865956907645092230336753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140577304605096728153557835 210865956907645092230336753)
      ·
        refine ⟨158149467680733819172752565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210865956907645092230336753 158149467680733819172752565)
        ·
          refine ⟨14826512595068795547445553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 158149467680733819172752565 14826512595068795547445553)
          ·
            refine ⟨11119884446301596660584165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14826512595068795547445553 11119884446301596660584165)
            ·
              refine ⟨2084978333681549373859531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11119884446301596660584165 2084978333681549373859531)
              ·
                refine ⟨3127467500522324060789297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2084978333681549373859531 3127467500522324060789297)
                ·
                  refine ⟨2345600625391743045591973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3127467500522324060789297 2345600625391743045591973)
                  ·
                    refine ⟨439800117260951821048495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2345600625391743045591973 439800117260951821048495)
                    ·
                      rfl

theorem cell23_2569523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 2, 4].length) (baseStart_2569523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569523 prefixEnd_2569523 := by exact prefixLift 2569523
  have htrace : WordTrace (prefixWord ++ tailWord_2569523) baseStart_2569523 baseEnd_2569523 := by
    simpa [prefixWord, tailWord_2569523, baseEnd_2569523] using wordTrace_append hprefix tailTrace_2569523
  have hstable : (prefixWord ++ tailWord_2569523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569523).length < 2 ^ (prefixWord ++ tailWord_2569523).sum := by decide
  have hdescent : baseEnd_2569523 < baseStart_2569523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569546 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 6, 1, 3]
def baseStart_2569546 : Nat := 118140960795 + 2569546 * 2 ^ 59
def prefixEnd_2569546 : Nat := 4983230072969 + 3 ^ 40 * 2569546 * 2
def baseEnd_2569546 : Nat := 1319412161837908873157879

theorem tailTrace_2569546 : CollatzResearch.WordTrace tailWord_2569546 prefixEnd_2569546 1319412161837908873157879 := by
  unfold tailWord_2569546
  simp only [CollatzResearch.WordTrace]
  refine ⟨23429760487245290090948123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62479361299320773575861661 23429760487245290090948123)
  ·
    refine ⟨35144640730867935136422185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23429760487245290090948123 35144640730867935136422185)
    ·
      refine ⟨26358480548150951352316639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35144640730867935136422185 26358480548150951352316639)
      ·
        refine ⟨39537720822226427028474959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26358480548150951352316639 39537720822226427028474959)
        ·
          refine ⟨59306581233339640542712439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39537720822226427028474959 59306581233339640542712439)
          ·
            refine ⟨88959871850009460814068659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59306581233339640542712439 88959871850009460814068659)
            ·
              refine ⟨133439807775014191221102989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88959871850009460814068659 133439807775014191221102989)
              ·
                refine ⟨50039927915630321707913621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133439807775014191221102989 50039927915630321707913621)
                ·
                  refine ⟨2345621621045171330058451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50039927915630321707913621 2345621621045171330058451)
                  ·
                    refine ⟨3518432431567756995087677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2345621621045171330058451 3518432431567756995087677)
                    ·
                      refine ⟨1319412161837908873157879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3518432431567756995087677 1319412161837908873157879)
                      ·
                        rfl

theorem cell23_2569546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 6, 1, 3].length) (baseStart_2569546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569546 prefixEnd_2569546 := by exact prefixLift 2569546
  have htrace : WordTrace (prefixWord ++ tailWord_2569546) baseStart_2569546 baseEnd_2569546 := by
    simpa [prefixWord, tailWord_2569546, baseEnd_2569546] using wordTrace_append hprefix tailTrace_2569546
  have hstable : (prefixWord ++ tailWord_2569546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569546).length < 2 ^ (prefixWord ++ tailWord_2569546).sum := by decide
  have hdescent : baseEnd_2569546 < baseStart_2569546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569599 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 4]
def baseStart_2569599 : Nat := 118140960795 + 2569599 * 2 ^ 59
def prefixEnd_2569599 : Nat := 4983230072969 + 3 ^ 40 * 2569599 * 2
def baseEnd_2569599 : Nat := 1319439376312597165795135

theorem tailTrace_2569599 : CollatzResearch.WordTrace tailWord_2569599 prefixEnd_2569599 1319439376312597165795135 := by
  unfold tailWord_2569599
  simp only [CollatzResearch.WordTrace]
  refine ⟨93720975017789150415471851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62480650011859433610314567 93720975017789150415471851)
  ·
    refine ⟨140581462526683725623207777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93720975017789150415471851 140581462526683725623207777)
    ·
      refine ⟨105436096895012794217405833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140581462526683725623207777 105436096895012794217405833)
      ·
        refine ⟨79077072671259595663054375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105436096895012794217405833 79077072671259595663054375)
        ·
          refine ⟨118615609006889393494581563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79077072671259595663054375 118615609006889393494581563)
          ·
            refine ⟨177923413510334090241872345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118615609006889393494581563 177923413510334090241872345)
            ·
              refine ⟨133442560132750567681404259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177923413510334090241872345 133442560132750567681404259)
              ·
                refine ⟨200163840199125851522106389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133442560132750567681404259 200163840199125851522106389)
                ·
                  refine ⟨9382680009334024290098737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 200163840199125851522106389 9382680009334024290098737)
                  ·
                    refine ⟨7037010007000518217574053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9382680009334024290098737 7037010007000518217574053)
                    ·
                      refine ⟨1319439376312597165795135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7037010007000518217574053 1319439376312597165795135)
                      ·
                        rfl

theorem cell23_2569599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_2569599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569599 prefixEnd_2569599 := by exact prefixLift 2569599
  have htrace : WordTrace (prefixWord ++ tailWord_2569599) baseStart_2569599 baseEnd_2569599 := by
    simpa [prefixWord, tailWord_2569599, baseEnd_2569599] using wordTrace_append hprefix tailTrace_2569599
  have hstable : (prefixWord ++ tailWord_2569599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569599).length < 2 ^ (prefixWord ++ tailWord_2569599).sum := by decide
  have hdescent : baseEnd_2569599 < baseStart_2569599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569603 : List Nat := [1, 1, 1, 3, 5, 1, 2, 2, 1, 4, 2]
def baseStart_2569603 : Nat := 118140960795 + 2569603 * 2 ^ 59
def prefixEnd_2569603 : Nat := 4983230072969 + 3 ^ 40 * 2569603 * 2
def baseEnd_2569603 : Nat := 1319441430235215150145117

theorem tailTrace_2569603 : CollatzResearch.WordTrace tailWord_2569603 prefixEnd_2569603 1319441430235215150145117 := by
  unfold tailWord_2569603
  simp only [CollatzResearch.WordTrace]
  refine ⟨93721120909774659098617463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62480747273183106065744975 93721120909774659098617463)
  ·
    refine ⟨140581681364661988647926195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93721120909774659098617463 140581681364661988647926195)
    ·
      refine ⟨210872522046992982971889293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140581681364661988647926195 210872522046992982971889293)
      ·
        refine ⟨79077195767622368614458485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210872522046992982971889293 79077195767622368614458485)
        ·
          refine ⟨7413487103214597057605483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79077195767622368614458485 7413487103214597057605483)
          ·
            refine ⟨11120230654821895586408225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7413487103214597057605483 11120230654821895586408225)
            ·
              refine ⟨8340172991116421689806169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11120230654821895586408225 8340172991116421689806169)
              ·
                refine ⟨6255129743337316267354627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8340172991116421689806169 6255129743337316267354627)
                ·
                  refine ⟨9382694615005974401031941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6255129743337316267354627 9382694615005974401031941)
                  ·
                    refine ⟨1759255240313620200193489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9382694615005974401031941 1759255240313620200193489)
                    ·
                      refine ⟨1319441430235215150145117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1759255240313620200193489 1319441430235215150145117)
                      ·
                        rfl

theorem cell23_2569603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 4, 2].length) (baseStart_2569603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569603 prefixEnd_2569603 := by exact prefixLift 2569603
  have htrace : WordTrace (prefixWord ++ tailWord_2569603) baseStart_2569603 baseEnd_2569603 := by
    simpa [prefixWord, tailWord_2569603, baseEnd_2569603] using wordTrace_append hprefix tailTrace_2569603
  have hstable : (prefixWord ++ tailWord_2569603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569603).length < 2 ^ (prefixWord ++ tailWord_2569603).sum := by decide
  have hdescent : baseEnd_2569603 < baseStart_2569603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569607 : List Nat := [1, 1, 4, 2, 2, 4, 2, 1, 1, 3, 2]
def baseStart_2569607 : Nat := 118140960795 + 2569607 * 2 ^ 59
def prefixEnd_2569607 : Nat := 4983230072969 + 3 ^ 40 * 2569607 * 2
def baseEnd_2569607 : Nat := 1319443484157833134495099

theorem tailTrace_2569607 : CollatzResearch.WordTrace tailWord_2569607 prefixEnd_2569607 1319443484157833134495099 := by
  unfold tailWord_2569607
  simp only [CollatzResearch.WordTrace]
  refine ⟨93721266801760167781763075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62480844534506778521175383 93721266801760167781763075)
  ·
    refine ⟨140581900202640251672644613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93721266801760167781763075 140581900202640251672644613)
    ·
      refine ⟨26359106287995047188620865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140581900202640251672644613 26359106287995047188620865)
      ·
        refine ⟨19769329715996285391465649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26359106287995047188620865 19769329715996285391465649)
        ·
          refine ⟨14826997286997214043599237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19769329715996285391465649 14826997286997214043599237)
          ·
            refine ⟨2780061991311977633174857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14826997286997214043599237 2780061991311977633174857)
            ·
              refine ⟨2085046493483983224881143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2780061991311977633174857 2085046493483983224881143)
              ·
                refine ⟨3127569740225974837321715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2085046493483983224881143 3127569740225974837321715)
                ·
                  refine ⟨4691354610338962255982573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3127569740225974837321715 4691354610338962255982573)
                  ·
                    refine ⟨1759257978877110845993465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4691354610338962255982573 1759257978877110845993465)
                    ·
                      refine ⟨1319443484157833134495099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1759257978877110845993465 1319443484157833134495099)
                      ·
                        rfl

theorem cell23_2569607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_2569607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569607 prefixEnd_2569607 := by exact prefixLift 2569607
  have htrace : WordTrace (prefixWord ++ tailWord_2569607) baseStart_2569607 baseEnd_2569607 := by
    simpa [prefixWord, tailWord_2569607, baseEnd_2569607] using wordTrace_append hprefix tailTrace_2569607
  have hstable : (prefixWord ++ tailWord_2569607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569607).length < 2 ^ (prefixWord ++ tailWord_2569607).sum := by decide
  have hdescent : baseEnd_2569607 < baseStart_2569607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569614 : List Nat := [4, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3]
def baseStart_2569614 : Nat := 118140960795 + 2569614 * 2 ^ 59
def prefixEnd_2569614 : Nat := 4983230072969 + 3 ^ 40 * 2569614 * 2
def baseEnd_2569614 : Nat := 1319447078522414607107567

theorem tailTrace_2569614 : CollatzResearch.WordTrace tailWord_2569614 prefixEnd_2569614 1319447078522414607107567 := by
  unfold tailWord_2569614
  simp only [CollatzResearch.WordTrace]
  refine ⟨11715190264091850997158487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62481014741823205318178597 11715190264091850997158487)
  ·
    refine ⟨17572785396137776495737731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11715190264091850997158487 17572785396137776495737731)
    ·
      refine ⟨26359178094206664743606597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17572785396137776495737731 26359178094206664743606597)
      ·
        refine ⟨4942345892663749639426237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26359178094206664743606597 4942345892663749639426237)
        ·
          refine ⟨1853379709748906114784839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4942345892663749639426237 1853379709748906114784839)
          ·
            refine ⟨2780069564623359172177259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1853379709748906114784839 2780069564623359172177259)
            ·
              refine ⟨4170104346935038758265889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2780069564623359172177259 4170104346935038758265889)
              ·
                refine ⟨3127578260201279068699417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4170104346935038758265889 3127578260201279068699417)
                ·
                  refine ⟨2345683695150959301524563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3127578260201279068699417 2345683695150959301524563)
                  ·
                    refine ⟨3518525542726438952286845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2345683695150959301524563 3518525542726438952286845)
                    ·
                      refine ⟨1319447078522414607107567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3518525542726438952286845 1319447078522414607107567)
                      ·
                        rfl

theorem cell23_2569614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_2569614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569614 prefixEnd_2569614 := by exact prefixLift 2569614
  have htrace : WordTrace (prefixWord ++ tailWord_2569614) baseStart_2569614 baseEnd_2569614 := by
    simpa [prefixWord, tailWord_2569614, baseEnd_2569614] using wordTrace_append hprefix tailTrace_2569614
  have hstable : (prefixWord ++ tailWord_2569614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569614).length < 2 ^ (prefixWord ++ tailWord_2569614).sum := by decide
  have hdescent : baseEnd_2569614 < baseStart_2569614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569626 : List Nat := [3, 1, 1, 4, 1, 1, 4, 1, 7]
def baseStart_2569626 : Nat := 118140960795 + 2569626 * 2 ^ 59
def prefixEnd_2569626 : Nat := 4983230072969 + 3 ^ 40 * 2569626 * 2
def baseEnd_2569626 : Nat := 146605915587807617795279

theorem tailTrace_2569626 : CollatzResearch.WordTrace tailWord_2569626 prefixEnd_2569626 146605915587807617795279 := by
  unfold tailWord_2569626
  simp only [CollatzResearch.WordTrace]
  refine ⟨23430489947172833506676183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62481306525794222684469821 23430489947172833506676183)
  ·
    refine ⟨35145734920759250260014275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23430489947172833506676183 35145734920759250260014275)
    ·
      refine ⟨52718602381138875390021413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35145734920759250260014275 52718602381138875390021413)
      ·
        refine ⟨9884737946463539135629015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52718602381138875390021413 9884737946463539135629015)
        ·
          refine ⟨14827106919695308703443523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9884737946463539135629015 14827106919695308703443523)
          ·
            refine ⟨22240660379542963055165285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14827106919695308703443523 22240660379542963055165285)
            ·
              refine ⟨4170123821164305572843491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22240660379542963055165285 4170123821164305572843491)
              ·
                refine ⟨6255185731746458359265237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4170123821164305572843491 6255185731746458359265237)
                ·
                  refine ⟨146605915587807617795279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6255185731746458359265237 146605915587807617795279)
                  ·
                    rfl

theorem cell23_2569626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 7].length) (baseStart_2569626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569626 prefixEnd_2569626 := by exact prefixLift 2569626
  have htrace : WordTrace (prefixWord ++ tailWord_2569626) baseStart_2569626 baseEnd_2569626 := by
    simpa [prefixWord, tailWord_2569626, baseEnd_2569626] using wordTrace_append hprefix tailTrace_2569626
  have hstable : (prefixWord ++ tailWord_2569626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569626).length < 2 ^ (prefixWord ++ tailWord_2569626).sum := by decide
  have hdescent : baseEnd_2569626 < baseStart_2569626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569696 : List Nat := [2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 3]
def baseStart_2569696 : Nat := 118140960795 + 2569696 * 2 ^ 59
def prefixEnd_2569696 : Nat := 4983230072969 + 3 ^ 40 * 2569696 * 2
def baseEnd_2569696 : Nat := 1319489183936083286282189

theorem tailTrace_2569696 : CollatzResearch.WordTrace tailWord_2569696 prefixEnd_2569696 1319489183936083286282189 := by
  unfold tailWord_2569696
  simp only [CollatzResearch.WordTrace]
  refine ⟨46862256449218867990876471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62483008598958490654501961 46862256449218867990876471)
  ·
    refine ⟨70293384673828301986314707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46862256449218867990876471 70293384673828301986314707)
    ·
      refine ⟨105440077010742452979472061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70293384673828301986314707 105440077010742452979472061)
      ·
        refine ⟨39540028879028419867302023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105440077010742452979472061 39540028879028419867302023)
        ·
          refine ⟨59310043318542629800953035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39540028879028419867302023 59310043318542629800953035)
          ·
            refine ⟨88965064977813944701429553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59310043318542629800953035 88965064977813944701429553)
            ·
              refine ⟨66723798733360458526072165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88965064977813944701429553 66723798733360458526072165)
              ·
                refine ⟨12510712262505085973638531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66723798733360458526072165 12510712262505085973638531)
                ·
                  refine ⟨18766068393757628960457797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12510712262505085973638531 18766068393757628960457797)
                  ·
                    refine ⟨3518637823829555430085837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18766068393757628960457797 3518637823829555430085837)
                    ·
                      refine ⟨1319489183936083286282189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3518637823829555430085837 1319489183936083286282189)
                      ·
                        rfl

theorem cell23_2569696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_2569696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569696 prefixEnd_2569696 := by exact prefixLift 2569696
  have htrace : WordTrace (prefixWord ++ tailWord_2569696) baseStart_2569696 baseEnd_2569696 := by
    simpa [prefixWord, tailWord_2569696, baseEnd_2569696] using wordTrace_append hprefix tailTrace_2569696
  have hstable : (prefixWord ++ tailWord_2569696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569696).length < 2 ^ (prefixWord ++ tailWord_2569696).sum := by decide
  have hdescent : baseEnd_2569696 < baseStart_2569696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569713 : List Nat := [1, 2, 2, 2, 3, 2, 1, 3, 2, 2, 3]
def baseStart_2569713 : Nat := 118140960795 + 2569713 * 2 ^ 59
def prefixEnd_2569713 : Nat := 4983230072969 + 3 ^ 40 * 2569713 * 2
def baseEnd_2569713 : Nat := 1319497913107209719769611

theorem tailTrace_2569713 : CollatzResearch.WordTrace tailWord_2569713 prefixEnd_2569713 1319497913107209719769611 := by
  unfold tailWord_2569713
  simp only [CollatzResearch.WordTrace]
  refine ⟨93725132939376147885121793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62483421959584098590081195 93725132939376147885121793)
  ·
    refine ⟨70293849704532110913841345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93725132939376147885121793 70293849704532110913841345)
    ·
      refine ⟨52720387278399083185381009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70293849704532110913841345 52720387278399083185381009)
      ·
        refine ⟨39540290458799312389035757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52720387278399083185381009 39540290458799312389035757)
        ·
          refine ⟨14827608922049742145888409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39540290458799312389035757 14827608922049742145888409)
          ·
            refine ⟨11120706691537306609416307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14827608922049742145888409 11120706691537306609416307)
            ·
              refine ⟨16681060037305959914124461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11120706691537306609416307 16681060037305959914124461)
              ·
                refine ⟨6255397513989734967796673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16681060037305959914124461 6255397513989734967796673)
                ·
                  refine ⟨4691548135492301225847505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6255397513989734967796673 4691548135492301225847505)
                  ·
                    refine ⟨3518661101619225919385629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4691548135492301225847505 3518661101619225919385629)
                    ·
                      refine ⟨1319497913107209719769611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3518661101619225919385629 1319497913107209719769611)
                      ·
                        rfl

theorem cell23_2569713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_2569713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569713 prefixEnd_2569713 := by exact prefixLift 2569713
  have htrace : WordTrace (prefixWord ++ tailWord_2569713) baseStart_2569713 baseEnd_2569713 := by
    simpa [prefixWord, tailWord_2569713, baseEnd_2569713] using wordTrace_append hprefix tailTrace_2569713
  have hstable : (prefixWord ++ tailWord_2569713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569713).length < 2 ^ (prefixWord ++ tailWord_2569713).sum := by decide
  have hdescent : baseEnd_2569713 < baseStart_2569713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569756 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 2, 1, 7]
def baseStart_2569756 : Nat := 118140960795 + 2569756 * 2 ^ 59
def prefixEnd_2569756 : Nat := 4983230072969 + 3 ^ 40 * 2569756 * 2
def baseEnd_2569756 : Nat := 1319519992775353051531913

theorem tailTrace_2569756 : CollatzResearch.WordTrace tailWord_2569756 prefixEnd_2569756 1319519992775353051531913 := by
  unfold tailWord_2569756
  simp only [CollatzResearch.WordTrace]
  refine ⟨46863350639110183114468561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62484467518813577485958081 46863350639110183114468561)
  ·
    refine ⟨35147512979332637335851421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46863350639110183114468561 35147512979332637335851421)
    ·
      refine ⟨13180317367249739000944283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35147512979332637335851421 13180317367249739000944283)
      ·
        refine ⟨19770476050874608501416425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13180317367249739000944283 19770476050874608501416425)
        ·
          refine ⟨14827857038155956376062319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19770476050874608501416425 14827857038155956376062319)
          ·
            refine ⟨22241785557233934564093479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14827857038155956376062319 22241785557233934564093479)
            ·
              refine ⟨33362678335850901846140219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22241785557233934564093479 33362678335850901846140219)
              ·
                refine ⟨50044017503776352769210329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33362678335850901846140219 50044017503776352769210329)
                ·
                  refine ⟨37533013127832264576907747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50044017503776352769210329 37533013127832264576907747)
                  ·
                    refine ⟨56299519691748396865361621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37533013127832264576907747 56299519691748396865361621)
                    ·
                      refine ⟨1319519992775353051531913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 56299519691748396865361621 1319519992775353051531913)
                      ·
                        rfl

theorem cell23_2569756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_2569756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569756 prefixEnd_2569756 := by exact prefixLift 2569756
  have htrace : WordTrace (prefixWord ++ tailWord_2569756) baseStart_2569756 baseEnd_2569756 := by
    simpa [prefixWord, tailWord_2569756, baseEnd_2569756] using wordTrace_append hprefix tailTrace_2569756
  have hstable : (prefixWord ++ tailWord_2569756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569756).length < 2 ^ (prefixWord ++ tailWord_2569756).sum := by decide
  have hdescent : baseEnd_2569756 < baseStart_2569756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569760 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 5, 1, 3]
def baseStart_2569760 : Nat := 118140960795 + 2569760 * 2 ^ 59
def prefixEnd_2569760 : Nat := 4983230072969 + 3 ^ 40 * 2569760 * 2
def baseEnd_2569760 : Nat := 1319522046697971035881895

theorem tailTrace_2569760 : CollatzResearch.WordTrace tailWord_2569760 prefixEnd_2569760 1319522046697971035881895 := by
  unfold tailWord_2569760
  simp only [CollatzResearch.WordTrace]
  refine ⟨46863423585102937456041367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62484564780137249941388489 46863423585102937456041367)
  ·
    refine ⟨70295135377654406184062051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46863423585102937456041367 70295135377654406184062051)
    ·
      refine ⟨105442703066481609276093077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70295135377654406184062051 105442703066481609276093077)
      ·
        refine ⟨4942626706241325434816863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 105442703066481609276093077 4942626706241325434816863)
        ·
          refine ⟨7413940059361988152225295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4942626706241325434816863 7413940059361988152225295)
          ·
            refine ⟨11120910089042982228337943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7413940059361988152225295 11120910089042982228337943)
            ·
              refine ⟨16681365133564473342506915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11120910089042982228337943 16681365133564473342506915)
              ·
                refine ⟨25022047700346710013760373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16681365133564473342506915 25022047700346710013760373)
                ·
                  refine ⟨2345816971907504063790035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25022047700346710013760373 2345816971907504063790035)
                  ·
                    refine ⟨3518725457861256095685053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2345816971907504063790035 3518725457861256095685053)
                    ·
                      refine ⟨1319522046697971035881895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3518725457861256095685053 1319522046697971035881895)
                      ·
                        rfl

theorem cell23_2569760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_2569760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569760 prefixEnd_2569760 := by exact prefixLift 2569760
  have htrace : WordTrace (prefixWord ++ tailWord_2569760) baseStart_2569760 baseEnd_2569760 := by
    simpa [prefixWord, tailWord_2569760, baseEnd_2569760] using wordTrace_append hprefix tailTrace_2569760
  have hstable : (prefixWord ++ tailWord_2569760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569760).length < 2 ^ (prefixWord ++ tailWord_2569760).sum := by decide
  have hdescent : baseEnd_2569760 < baseStart_2569760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569770 : List Nat := [3, 1, 4, 1, 1, 1, 3, 1, 1, 5, 2]
def baseStart_2569770 : Nat := 118140960795 + 2569770 * 2 ^ 59
def prefixEnd_2569770 : Nat := 4983230072969 + 3 ^ 40 * 2569770 * 2
def baseEnd_2569770 : Nat := 1319527181504515996756849

theorem tailTrace_2569770 : CollatzResearch.WordTrace tailWord_2569770 prefixEnd_2569770 1319527181504515996756849 := by
  unfold tailWord_2569770
  simp only [CollatzResearch.WordTrace]
  refine ⟨23431802975042411654986691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62484807933446431079964509 23431802975042411654986691)
  ·
    refine ⟨35147704462563617482480037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23431802975042411654986691 35147704462563617482480037)
    ·
      refine ⟨6590194586730678277965007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35147704462563617482480037 6590194586730678277965007)
      ·
        refine ⟨9885291880096017416947511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6590194586730678277965007 9885291880096017416947511)
        ·
          refine ⟨14827937820144026125421267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9885291880096017416947511 14827937820144026125421267)
          ·
            refine ⟨22241906730216039188131901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14827937820144026125421267 22241906730216039188131901)
            ·
              refine ⟨8340715023831014695549463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22241906730216039188131901 8340715023831014695549463)
              ·
                refine ⟨12511072535746522043324195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8340715023831014695549463 12511072535746522043324195)
                ·
                  refine ⟨18766608803619783064986293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12511072535746522043324195 18766608803619783064986293)
                  ·
                    refine ⟨1759369575339354662342465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18766608803619783064986293 1759369575339354662342465)
                    ·
                      refine ⟨1319527181504515996756849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1759369575339354662342465 1319527181504515996756849)
                      ·
                        rfl

theorem cell23_2569770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_2569770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569770 prefixEnd_2569770 := by exact prefixLift 2569770
  have htrace : WordTrace (prefixWord ++ tailWord_2569770) baseStart_2569770 baseEnd_2569770 := by
    simpa [prefixWord, tailWord_2569770, baseEnd_2569770] using wordTrace_append hprefix tailTrace_2569770
  have hstable : (prefixWord ++ tailWord_2569770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569770).length < 2 ^ (prefixWord ++ tailWord_2569770).sum := by decide
  have hdescent : baseEnd_2569770 < baseStart_2569770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569806 : List Nat := [4, 1, 1, 1, 1, 2, 1, 12]
def baseStart_2569806 : Nat := 118140960795 + 2569806 * 2 ^ 59
def prefixEnd_2569806 : Nat := 4983230072969 + 3 ^ 40 * 2569806 * 2
def baseEnd_2569806 : Nat := 48872061733632513181729

theorem tailTrace_2569806 : CollatzResearch.WordTrace tailWord_2569806 prefixEnd_2569806 48872061733632513181729 := by
  unfold tailWord_2569806
  simp only [CollatzResearch.WordTrace]
  refine ⟨11716065616004903096032159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62485683285359483178838181 11716065616004903096032159)
  ·
    refine ⟨17574098424007354644048239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11716065616004903096032159 17574098424007354644048239)
    ·
      refine ⟨26361147636011031966072359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17574098424007354644048239 26361147636011031966072359)
      ·
        refine ⟨39541721454016547949108539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26361147636011031966072359 39541721454016547949108539)
        ·
          refine ⟨59312582181024821923662809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39541721454016547949108539 59312582181024821923662809)
          ·
            refine ⟨44484436635768616442747107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59312582181024821923662809 44484436635768616442747107)
            ·
              refine ⟨66726654953652924664120661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44484436635768616442747107 66726654953652924664120661)
              ·
                refine ⟨48872061733632513181729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 66726654953652924664120661 48872061733632513181729)
                ·
                  rfl

theorem cell23_2569806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 12].length) (baseStart_2569806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569806 prefixEnd_2569806 := by exact prefixLift 2569806
  have htrace : WordTrace (prefixWord ++ tailWord_2569806) baseStart_2569806 baseEnd_2569806 := by
    simpa [prefixWord, tailWord_2569806, baseEnd_2569806] using wordTrace_append hprefix tailTrace_2569806
  have hstable : (prefixWord ++ tailWord_2569806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569806).length < 2 ^ (prefixWord ++ tailWord_2569806).sum := by decide
  have hdescent : baseEnd_2569806 < baseStart_2569806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569810 : List Nat := [3, 2, 2, 1, 2, 4, 1, 1, 1, 6]
def baseStart_2569810 : Nat := 118140960795 + 2569810 * 2 ^ 59
def prefixEnd_2569810 : Nat := 4983230072969 + 3 ^ 40 * 2569810 * 2
def baseEnd_2569810 : Nat := 439849240243565280085555

theorem tailTrace_2569810 : CollatzResearch.WordTrace tailWord_2569810 prefixEnd_2569810 439849240243565280085555 := by
  unfold tailWord_2569810
  simp only [CollatzResearch.WordTrace]
  refine ⟨23432167705006183362850721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62485780546683155634268589 23432167705006183362850721)
  ·
    refine ⟨17574125778754637522138041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23432167705006183362850721 17574125778754637522138041)
    ·
      refine ⟨13180594334065978141603531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17574125778754637522138041 13180594334065978141603531)
      ·
        refine ⟨19770891501098967212405297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13180594334065978141603531 19770891501098967212405297)
        ·
          refine ⟨14828168625824225409303973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19770891501098967212405297 14828168625824225409303973)
          ·
            refine ⟨2780281617342042264244495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14828168625824225409303973 2780281617342042264244495)
            ·
              refine ⟨4170422426013063396366743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2780281617342042264244495 4170422426013063396366743)
              ·
                refine ⟨6255633639019595094550115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4170422426013063396366743 6255633639019595094550115)
                ·
                  refine ⟨9383450458529392641825173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6255633639019595094550115 9383450458529392641825173)
                  ·
                    refine ⟨439849240243565280085555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9383450458529392641825173 439849240243565280085555)
                    ·
                      rfl

theorem cell23_2569810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_2569810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569810 prefixEnd_2569810 := by exact prefixLift 2569810
  have htrace : WordTrace (prefixWord ++ tailWord_2569810) baseStart_2569810 baseEnd_2569810 := by
    simpa [prefixWord, tailWord_2569810, baseEnd_2569810] using wordTrace_append hprefix tailTrace_2569810
  have hstable : (prefixWord ++ tailWord_2569810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569810).length < 2 ^ (prefixWord ++ tailWord_2569810).sum := by decide
  have hdescent : baseEnd_2569810 < baseStart_2569810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569833 : List Nat := [1, 2, 1, 1, 1, 4, 2, 4, 1, 3, 3]
def baseStart_2569833 : Nat := 118140960795 + 2569833 * 2 ^ 59
def prefixEnd_2569833 : Nat := 4983230072969 + 3 ^ 40 * 2569833 * 2
def baseEnd_2569833 : Nat := 1319559530785749250269059

theorem tailTrace_2569833 : CollatzResearch.WordTrace tailWord_2569833 prefixEnd_2569833 1319559530785749250269059 := by
  unfold tailWord_2569833
  simp only [CollatzResearch.WordTrace]
  refine ⟨93729509698941408379490153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62486339799294272252993435 93729509698941408379490153)
  ·
    refine ⟨70297132274206056284617615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93729509698941408379490153 70297132274206056284617615)
    ·
      refine ⟨105445698411309084426926423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70297132274206056284617615 105445698411309084426926423)
      ·
        refine ⟨158168547616963626640389635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105445698411309084426926423 158168547616963626640389635)
        ·
          refine ⟨237252821425445439960584453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158168547616963626640389635 237252821425445439960584453)
          ·
            refine ⟨44484904017271019992609585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 237252821425445439960584453 44484904017271019992609585)
            ·
              refine ⟨33363678012953264994457189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44484904017271019992609585 33363678012953264994457189)
              ·
                refine ⟨6255689627428737186460723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33363678012953264994457189 6255689627428737186460723)
                ·
                  refine ⟨9383534441143105779691085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6255689627428737186460723 9383534441143105779691085)
                  ·
                    refine ⟨3518825415428664667384157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9383534441143105779691085 3518825415428664667384157)
                    ·
                      refine ⟨1319559530785749250269059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3518825415428664667384157 1319559530785749250269059)
                      ·
                        rfl

theorem cell23_2569833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 3, 3].length) (baseStart_2569833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569833 prefixEnd_2569833 := by exact prefixLift 2569833
  have htrace : WordTrace (prefixWord ++ tailWord_2569833) baseStart_2569833 baseEnd_2569833 := by
    simpa [prefixWord, tailWord_2569833, baseEnd_2569833] using wordTrace_append hprefix tailTrace_2569833
  have hstable : (prefixWord ++ tailWord_2569833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569833).length < 2 ^ (prefixWord ++ tailWord_2569833).sum := by decide
  have hdescent : baseEnd_2569833 < baseStart_2569833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569836 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 1, 9]
def baseStart_2569836 : Nat := 118140960795 + 2569836 * 2 ^ 59
def prefixEnd_2569836 : Nat := 4983230072969 + 3 ^ 40 * 2569836 * 2
def baseEnd_2569836 : Nat := 439853690409237579510515

theorem tailTrace_2569836 : CollatzResearch.WordTrace tailWord_2569836 prefixEnd_2569836 439853690409237579510515 := by
  unfold tailWord_2569836
  simp only [CollatzResearch.WordTrace]
  refine ⟨46864809558965269945924681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62486412745287026594566241 46864809558965269945924681)
  ·
    refine ⟨35148607169223952459443511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46864809558965269945924681 35148607169223952459443511)
    ·
      refine ⟨52722910753835928689165267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35148607169223952459443511 52722910753835928689165267)
      ·
        refine ⟨79084366130753893033747901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52722910753835928689165267 79084366130753893033747901)
        ·
          refine ⟨29656637299032709887655463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79084366130753893033747901 29656637299032709887655463)
          ·
            refine ⟨44484955948549064831483195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29656637299032709887655463 44484955948549064831483195)
            ·
              refine ⟨66727433922823597247224793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44484955948549064831483195 66727433922823597247224793)
              ·
                refine ⟨50045575442117697935418595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66727433922823597247224793 50045575442117697935418595)
                ·
                  refine ⟨75068363163176546903127893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50045575442117697935418595 75068363163176546903127893)
                  ·
                    refine ⟨439853690409237579510515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 75068363163176546903127893 439853690409237579510515)
                    ·
                      rfl

theorem cell23_2569836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 9].length) (baseStart_2569836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569836 prefixEnd_2569836 := by exact prefixLift 2569836
  have htrace : WordTrace (prefixWord ++ tailWord_2569836) baseStart_2569836 baseEnd_2569836 := by
    simpa [prefixWord, tailWord_2569836, baseEnd_2569836] using wordTrace_append hprefix tailTrace_2569836
  have hstable : (prefixWord ++ tailWord_2569836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569836).length < 2 ^ (prefixWord ++ tailWord_2569836).sum := by decide
  have hdescent : baseEnd_2569836 < baseStart_2569836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569843 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 1, 9, 2]
def baseStart_2569843 : Nat := 118140960795 + 2569843 * 2 ^ 59
def prefixEnd_2569843 : Nat := 4983230072969 + 3 ^ 40 * 2569843 * 2
def baseEnd_2569843 : Nat := 1319564665592294211144013

theorem tailTrace_2569843 : CollatzResearch.WordTrace tailWord_2569843 prefixEnd_2569843 1319564665592294211144013 := by
  unfold tailWord_2569843
  simp only [CollatzResearch.WordTrace]
  refine ⟨93729874428905180087354183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62486582952603453391569455 93729874428905180087354183)
  ·
    refine ⟨140594811643357770131031275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93729874428905180087354183 140594811643357770131031275)
    ·
      refine ⟨210892217465036655196546913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140594811643357770131031275 210892217465036655196546913)
      ·
        refine ⟨158169163098777491397410185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210892217465036655196546913 158169163098777491397410185)
        ·
          refine ⟨118626872324083118548057639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158169163098777491397410185 118626872324083118548057639)
          ·
            refine ⟨177940308486124677822086459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118626872324083118548057639 177940308486124677822086459)
            ·
              refine ⟨266910462729187016733129689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177940308486124677822086459 266910462729187016733129689)
              ·
                refine ⟨200182847046890262549847267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 266910462729187016733129689 200182847046890262549847267)
                ·
                  refine ⟨300274270570335393824770901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 200182847046890262549847267 300274270570335393824770901)
                  ·
                    refine ⟨1759419554123058948192017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 300274270570335393824770901 1759419554123058948192017)
                    ·
                      refine ⟨1319564665592294211144013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1759419554123058948192017 1319564665592294211144013)
                      ·
                        rfl

theorem cell23_2569843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 9, 2].length) (baseStart_2569843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569843 prefixEnd_2569843 := by exact prefixLift 2569843
  have htrace : WordTrace (prefixWord ++ tailWord_2569843) baseStart_2569843 baseEnd_2569843 := by
    simpa [prefixWord, tailWord_2569843, baseEnd_2569843] using wordTrace_append hprefix tailTrace_2569843
  have hstable : (prefixWord ++ tailWord_2569843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569843).length < 2 ^ (prefixWord ++ tailWord_2569843).sum := by decide
  have hdescent : baseEnd_2569843 < baseStart_2569843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569893 : List Nat := [1, 3, 1, 2, 1, 2, 4, 1, 2, 1, 5]
def baseStart_2569893 : Nat := 118140960795 + 2569893 * 2 ^ 59
def prefixEnd_2569893 : Nat := 4983230072969 + 3 ^ 40 * 2569893 * 2
def baseEnd_2569893 : Nat := 1319590339625019015518783

theorem tailTrace_2569893 : CollatzResearch.WordTrace tailWord_2569893 prefixEnd_2569893 1319590339625019015518783 := by
  unfold tailWord_2569893
  simp only [CollatzResearch.WordTrace]
  refine ⟨93731698078724038626674333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62487798719149359084449555 93731698078724038626674333)
  ·
    refine ⟨35149386779521514485002875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93731698078724038626674333 35149386779521514485002875)
    ·
      refine ⟨52724080169282271727504313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35149386779521514485002875 52724080169282271727504313)
      ·
        refine ⟨39543060126961703795628235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52724080169282271727504313 39543060126961703795628235)
        ·
          refine ⟨59314590190442555693442353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39543060126961703795628235 59314590190442555693442353)
          ·
            refine ⟨44485942642831916770081765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59314590190442555693442353 44485942642831916770081765)
            ·
              refine ⟨8341114245530984394390331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44485942642831916770081765 8341114245530984394390331)
              ·
                refine ⟨12511671368296476591585497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8341114245530984394390331 12511671368296476591585497)
                ·
                  refine ⟨9383753526222357443689123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12511671368296476591585497 9383753526222357443689123)
                  ·
                    refine ⟨14075630289333536165533685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9383753526222357443689123 14075630289333536165533685)
                    ·
                      refine ⟨1319590339625019015518783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14075630289333536165533685 1319590339625019015518783)
                      ·
                        rfl

theorem cell23_2569893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_2569893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569893 prefixEnd_2569893 := by exact prefixLift 2569893
  have htrace : WordTrace (prefixWord ++ tailWord_2569893) baseStart_2569893 baseEnd_2569893 := by
    simpa [prefixWord, tailWord_2569893, baseEnd_2569893] using wordTrace_append hprefix tailTrace_2569893
  have hstable : (prefixWord ++ tailWord_2569893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569893).length < 2 ^ (prefixWord ++ tailWord_2569893).sum := by decide
  have hdescent : baseEnd_2569893 < baseStart_2569893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569902 : List Nat := [4, 1, 4, 1, 3, 1, 2, 2, 1, 2, 2]
def baseStart_2569902 : Nat := 118140960795 + 2569902 * 2 ^ 59
def prefixEnd_2569902 : Nat := 4983230072969 + 3 ^ 40 * 2569902 * 2
def baseEnd_2569902 : Nat := 1319594960950909480306243

theorem tailTrace_2569902 : CollatzResearch.WordTrace tailWord_2569902 prefixEnd_2569902 1319594960950909480306243 := by
  unfold tailWord_2569902
  simp only [CollatzResearch.WordTrace]
  refine ⟨11716503291961429145468995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62488017557127622109167973 11716503291961429145468995)
  ·
    refine ⟨17574754937942143718203493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11716503291961429145468995 17574754937942143718203493)
    ·
      refine ⟨3295266550864151947163155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17574754937942143718203493 3295266550864151947163155)
      ·
        refine ⟨4942899826296227920744733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3295266550864151947163155 4942899826296227920744733)
        ·
          refine ⟨1853587434861085470279275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4942899826296227920744733 1853587434861085470279275)
          ·
            refine ⟨2780381152291628205418913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1853587434861085470279275 2780381152291628205418913)
            ·
              refine ⟨2085285864218721154064185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2780381152291628205418913 2085285864218721154064185)
              ·
                refine ⟨1563964398164040865548139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2085285864218721154064185 1563964398164040865548139)
                ·
                  refine ⟨2345946597246061298322209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1563964398164040865548139 2345946597246061298322209)
                  ·
                    refine ⟨1759459947934545973741657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2345946597246061298322209 1759459947934545973741657)
                    ·
                      refine ⟨1319594960950909480306243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1759459947934545973741657 1319594960950909480306243)
                      ·
                        rfl

theorem cell23_2569902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_2569902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569902 prefixEnd_2569902 := by exact prefixLift 2569902
  have htrace : WordTrace (prefixWord ++ tailWord_2569902) baseStart_2569902 baseEnd_2569902 := by
    simpa [prefixWord, tailWord_2569902, baseEnd_2569902] using wordTrace_append hprefix tailTrace_2569902
  have hstable : (prefixWord ++ tailWord_2569902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569902).length < 2 ^ (prefixWord ++ tailWord_2569902).sum := by decide
  have hdescent : baseEnd_2569902 < baseStart_2569902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569903 : List Nat := [1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 4]
def baseStart_2569903 : Nat := 118140960795 + 2569903 * 2 ^ 59
def prefixEnd_2569903 : Nat := 4983230072969 + 3 ^ 40 * 2569903 * 2
def baseEnd_2569903 : Nat := 1319595474431563976393737

theorem tailTrace_2569903 : CollatzResearch.WordTrace tailWord_2569903 prefixEnd_2569903 1319595474431563976393737 := by
  unfold tailWord_2569903
  simp only [CollatzResearch.WordTrace]
  refine ⟨93732062808687810334538363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62488041872458540223025575 93732062808687810334538363)
  ·
    refine ⟨140598094213031715501807545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93732062808687810334538363 140598094213031715501807545)
    ·
      refine ⟨105448570659773786626355659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140598094213031715501807545 105448570659773786626355659)
      ·
        refine ⟨158172855989660679939533489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105448570659773786626355659 158172855989660679939533489)
        ·
          refine ⟨118629641992245509954650117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158172855989660679939533489 118629641992245509954650117)
          ·
            refine ⟨22243057873546033116496897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118629641992245509954650117 22243057873546033116496897)
            ·
              refine ⟨16682293405159524837372673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22243057873546033116496897 16682293405159524837372673)
              ·
                refine ⟨12511720053869643628029505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16682293405159524837372673 12511720053869643628029505)
                ·
                  refine ⟨9383790040402232721022129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12511720053869643628029505 9383790040402232721022129)
                  ·
                    refine ⟨7037842530301674540766597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9383790040402232721022129 7037842530301674540766597)
                    ·
                      refine ⟨1319595474431563976393737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7037842530301674540766597 1319595474431563976393737)
                      ·
                        rfl

theorem cell23_2569903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 4].length) (baseStart_2569903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569903 prefixEnd_2569903 := by exact prefixLift 2569903
  have htrace : WordTrace (prefixWord ++ tailWord_2569903) baseStart_2569903 baseEnd_2569903 := by
    simpa [prefixWord, tailWord_2569903, baseEnd_2569903] using wordTrace_append hprefix tailTrace_2569903
  have hstable : (prefixWord ++ tailWord_2569903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569903).length < 2 ^ (prefixWord ++ tailWord_2569903).sum := by decide
  have hdescent : baseEnd_2569903 < baseStart_2569903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569924 : List Nat := [2, 3, 3, 1, 1, 1, 1, 5, 2, 2, 2]
def baseStart_2569924 : Nat := 118140960795 + 2569924 * 2 ^ 59
def prefixEnd_2569924 : Nat := 4983230072969 + 3 ^ 40 * 2569924 * 2
def baseEnd_2569924 : Nat := 1319606257525308394231141

theorem tailTrace_2569924 : CollatzResearch.WordTrace tailWord_2569924 prefixEnd_2569924 1319606257525308394231141 := by
  unfold tailWord_2569924
  simp only [CollatzResearch.WordTrace]
  refine ⟨46866414370805865460526413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62488552494407820614035217 46866414370805865460526413)
  ·
    refine ⟨17574905389052199547697405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46866414370805865460526413 17574905389052199547697405)
    ·
      refine ⟨6590589520894574830386527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17574905389052199547697405 6590589520894574830386527)
      ·
        refine ⟨9885884281341862245579791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6590589520894574830386527 9885884281341862245579791)
        ·
          refine ⟨14828826422012793368369687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9885884281341862245579791 14828826422012793368369687)
          ·
            refine ⟨22243239633019190052554531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14828826422012793368369687 22243239633019190052554531)
            ·
              refine ⟨33364859449528785078831797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22243239633019190052554531 33364859449528785078831797)
              ·
                refine ⟨3127955573393323601140481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33364859449528785078831797 3127955573393323601140481)
                ·
                  refine ⟨2345966680044992700855361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3127955573393323601140481 2345966680044992700855361)
                  ·
                    refine ⟨1759475010033744525641521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2345966680044992700855361 1759475010033744525641521)
                    ·
                      refine ⟨1319606257525308394231141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1759475010033744525641521 1319606257525308394231141)
                      ·
                        rfl

theorem cell23_2569924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_2569924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569924 prefixEnd_2569924 := by exact prefixLift 2569924
  have htrace : WordTrace (prefixWord ++ tailWord_2569924) baseStart_2569924 baseEnd_2569924 := by
    simpa [prefixWord, tailWord_2569924, baseEnd_2569924] using wordTrace_append hprefix tailTrace_2569924
  have hstable : (prefixWord ++ tailWord_2569924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569924).length < 2 ^ (prefixWord ++ tailWord_2569924).sum := by decide
  have hdescent : baseEnd_2569924 < baseStart_2569924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569930 : List Nat := [3, 1, 2, 1, 5, 1, 1, 2, 7]
def baseStart_2569930 : Nat := 118140960795 + 2569930 * 2 ^ 59
def prefixEnd_2569930 : Nat := 4983230072969 + 3 ^ 40 * 2569930 * 2
def baseEnd_2569930 : Nat := 146623259823248374528457

theorem tailTrace_2569930 : CollatzResearch.WordTrace tailWord_2569930 prefixEnd_2569930 146623259823248374528457 := by
  unfold tailWord_2569930
  simp only [CollatzResearch.WordTrace]
  refine ⟨23433261894897498486442811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62488698386393329297180829 23433261894897498486442811)
  ·
    refine ⟨35149892842346247729664217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23433261894897498486442811 35149892842346247729664217)
    ·
      refine ⟨26362419631759685797248163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35149892842346247729664217 26362419631759685797248163)
      ·
        refine ⟨39543629447639528695872245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26362419631759685797248163 39543629447639528695872245)
        ·
          refine ⟨3707215260716205815238023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39543629447639528695872245 3707215260716205815238023)
          ·
            refine ⟨5560822891074308722857035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3707215260716205815238023 5560822891074308722857035)
            ·
              refine ⟨8341234336611463084285553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5560822891074308722857035 8341234336611463084285553)
              ·
                refine ⟨6255925752458597313214165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8341234336611463084285553 6255925752458597313214165)
                ·
                  refine ⟨146623259823248374528457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6255925752458597313214165 146623259823248374528457)
                  ·
                    rfl

theorem cell23_2569930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 7].length) (baseStart_2569930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569930 prefixEnd_2569930 := by exact prefixLift 2569930
  have htrace : WordTrace (prefixWord ++ tailWord_2569930) baseStart_2569930 baseEnd_2569930 := by
    simpa [prefixWord, tailWord_2569930, baseEnd_2569930] using wordTrace_append hprefix tailTrace_2569930
  have hstable : (prefixWord ++ tailWord_2569930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569930).length < 2 ^ (prefixWord ++ tailWord_2569930).sum := by decide
  have hdescent : baseEnd_2569930 < baseStart_2569930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569943 : List Nat := [1, 1, 3, 2, 1, 3, 3, 1, 1, 7]
def baseStart_2569943 : Nat := 118140960795 + 2569943 * 2 ^ 59
def prefixEnd_2569943 : Nat := 4983230072969 + 3 ^ 40 * 2569943 * 2
def baseEnd_2569943 : Nat := 439872004552581273297851

theorem tailTrace_2569943 : CollatzResearch.WordTrace tailWord_2569943 prefixEnd_2569943 439872004552581273297851 := by
  unfold tailWord_2569943
  simp only [CollatzResearch.WordTrace]
  refine ⟨93733521728542897165994483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62489014485695264777329655 93733521728542897165994483)
  ·
    refine ⟨140600282592814345748991725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93733521728542897165994483 140600282592814345748991725)
    ·
      refine ⟨52725105972305379655871897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140600282592814345748991725 52725105972305379655871897)
      ·
        refine ⟨39543829479229034741903923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52725105972305379655871897 39543829479229034741903923)
        ·
          refine ⟨59315744218843552112855885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39543829479229034741903923 59315744218843552112855885)
          ·
            refine ⟨22243404082066332042320957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59315744218843552112855885 22243404082066332042320957)
            ·
              refine ⟨8341276530774874515870359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22243404082066332042320957 8341276530774874515870359)
              ·
                refine ⟨12511914796162311773805539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8341276530774874515870359 12511914796162311773805539)
                ·
                  refine ⟨18767872194243467660708309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12511914796162311773805539 18767872194243467660708309)
                  ·
                    refine ⟨439872004552581273297851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18767872194243467660708309 439872004552581273297851)
                    ·
                      rfl

theorem cell23_2569943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 7].length) (baseStart_2569943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569943 prefixEnd_2569943 := by exact prefixLift 2569943
  have htrace : WordTrace (prefixWord ++ tailWord_2569943) baseStart_2569943 baseEnd_2569943 := by
    simpa [prefixWord, tailWord_2569943, baseEnd_2569943] using wordTrace_append hprefix tailTrace_2569943
  have hstable : (prefixWord ++ tailWord_2569943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569943).length < 2 ^ (prefixWord ++ tailWord_2569943).sum := by decide
  have hdescent : baseEnd_2569943 < baseStart_2569943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2569993 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 1, 6, 4]
def baseStart_2569993 : Nat := 118140960795 + 2569993 * 2 ^ 59
def prefixEnd_2569993 : Nat := 4983230072969 + 3 ^ 40 * 2569993 * 2
def baseEnd_2569993 : Nat := 1319641687690468624268323

theorem tailTrace_2569993 : CollatzResearch.WordTrace tailWord_2569993 prefixEnd_2569993 1319641687690468624268323 := by
  unfold tailWord_2569993
  simp only [CollatzResearch.WordTrace]
  refine ⟨93735345378361755705314633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62490230252241170470209755 93735345378361755705314633)
  ·
    refine ⟨70301509033771316778985975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93735345378361755705314633 70301509033771316778985975)
    ·
      refine ⟨105452263550656975168478963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70301509033771316778985975 105452263550656975168478963)
      ·
        refine ⟨158178395325985462752718445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105452263550656975168478963 158178395325985462752718445)
        ·
          refine ⟨59316898247244548532269417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158178395325985462752718445 59316898247244548532269417)
          ·
            refine ⟨44487673685433411399202063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59316898247244548532269417 44487673685433411399202063)
            ·
              refine ⟨66731510528150117098803095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44487673685433411399202063 66731510528150117098803095)
              ·
                refine ⟨100097265792225175648204643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66731510528150117098803095 100097265792225175648204643)
                ·
                  refine ⟨150145898688337763472306965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100097265792225175648204643 150145898688337763472306965)
                  ·
                    refine ⟨7038089001015832662764389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 150145898688337763472306965 7038089001015832662764389)
                    ·
                      refine ⟨1319641687690468624268323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7038089001015832662764389 1319641687690468624268323)
                      ·
                        rfl

theorem cell23_2569993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 6, 4].length) (baseStart_2569993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2569993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2569993 prefixEnd_2569993 := by exact prefixLift 2569993
  have htrace : WordTrace (prefixWord ++ tailWord_2569993) baseStart_2569993 baseEnd_2569993 := by
    simpa [prefixWord, tailWord_2569993, baseEnd_2569993] using wordTrace_append hprefix tailTrace_2569993
  have hstable : (prefixWord ++ tailWord_2569993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2569993).length < 2 ^ (prefixWord ++ tailWord_2569993).sum := by decide
  have hdescent : baseEnd_2569993 < baseStart_2569993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2569993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570017 : List Nat := [1, 2, 3, 2, 1, 4, 1, 2, 2, 2, 3]
def baseStart_2570017 : Nat := 118140960795 + 2570017 * 2 ^ 59
def prefixEnd_2570017 : Nat := 4983230072969 + 3 ^ 40 * 2570017 * 2
def baseEnd_2570017 : Nat := 1319654011226176530368213

theorem tailTrace_2570017 : CollatzResearch.WordTrace tailWord_2570017 prefixEnd_2570017 1319654011226176530368213 := by
  unfold tailWord_2570017
  simp only [CollatzResearch.WordTrace]
  refine ⟨93736220730274807804188305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62490813820183205202792203 93736220730274807804188305)
  ·
    refine ⟨70302165547706105853141229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93736220730274807804188305 70302165547706105853141229)
    ·
      refine ⟨26363312080389789694927961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70302165547706105853141229 26363312080389789694927961)
      ·
        refine ⟨19772484060292342271195971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26363312080389789694927961 19772484060292342271195971)
        ·
          refine ⟨29658726090438513406793957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19772484060292342271195971 29658726090438513406793957)
          ·
            refine ⟨5561011141957221263773867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29658726090438513406793957 5561011141957221263773867)
            ·
              refine ⟨8341516712935831895660801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5561011141957221263773867 8341516712935831895660801)
              ·
                refine ⟨6256137534701873921745601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8341516712935831895660801 6256137534701873921745601)
                ·
                  refine ⟨4692103151026405441309201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6256137534701873921745601 4692103151026405441309201)
                  ·
                    refine ⟨3519077363269804080981901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4692103151026405441309201 3519077363269804080981901)
                    ·
                      refine ⟨1319654011226176530368213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3519077363269804080981901 1319654011226176530368213)
                      ·
                        rfl

theorem cell23_2570017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_2570017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570017 prefixEnd_2570017 := by exact prefixLift 2570017
  have htrace : WordTrace (prefixWord ++ tailWord_2570017) baseStart_2570017 baseEnd_2570017 := by
    simpa [prefixWord, tailWord_2570017, baseEnd_2570017] using wordTrace_append hprefix tailTrace_2570017
  have hstable : (prefixWord ++ tailWord_2570017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570017).length < 2 ^ (prefixWord ++ tailWord_2570017).sum := by decide
  have hdescent : baseEnd_2570017 < baseStart_2570017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570020 : List Nat := [2, 3, 1, 3, 2, 1, 2, 1, 8]
def baseStart_2570020 : Nat := 118140960795 + 2570020 * 2 ^ 59
def prefixEnd_2570020 : Nat := 4983230072969 + 3 ^ 40 * 2570020 * 2
def baseEnd_2570020 : Nat := 146628394629793335403411

theorem tailTrace_2570020 : CollatzResearch.WordTrace tailWord_2570020 prefixEnd_2570020 146628394629793335403411 := by
  unfold tailWord_2570020
  simp only [CollatzResearch.WordTrace]
  refine ⟨46868165074631969658273757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62490886766175959544365009 46868165074631969658273757)
  ·
    refine ⟨17575561902986988621852659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46868165074631969658273757 17575561902986988621852659)
    ·
      refine ⟨26363342854480482932778989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17575561902986988621852659 26363342854480482932778989)
      ·
        refine ⟨9886253570430181099792121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26363342854480482932778989 9886253570430181099792121)
        ·
          refine ⟨7414690177822635824844091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9886253570430181099792121 7414690177822635824844091)
          ·
            refine ⟨11122035266733953737266137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7414690177822635824844091 11122035266733953737266137)
            ·
              refine ⟨8341526450050465302949603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11122035266733953737266137 8341526450050465302949603)
              ·
                refine ⟨12512289675075697954424405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8341526450050465302949603 12512289675075697954424405)
                ·
                  refine ⟨146628394629793335403411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12512289675075697954424405 146628394629793335403411)
                  ·
                    rfl

theorem cell23_2570020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 8].length) (baseStart_2570020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570020 prefixEnd_2570020 := by exact prefixLift 2570020
  have htrace : WordTrace (prefixWord ++ tailWord_2570020) baseStart_2570020 baseEnd_2570020 := by
    simpa [prefixWord, tailWord_2570020, baseEnd_2570020] using wordTrace_append hprefix tailTrace_2570020
  have hstable : (prefixWord ++ tailWord_2570020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570020).length < 2 ^ (prefixWord ++ tailWord_2570020).sum := by decide
  have hdescent : baseEnd_2570020 < baseStart_2570020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570024 : List Nat := [2, 1, 5, 1, 1, 4, 1, 1, 3, 4]
def baseStart_2570024 : Nat := 118140960795 + 2570024 * 2 ^ 59
def prefixEnd_2570024 : Nat := 4983230072969 + 3 ^ 40 * 2570024 * 2
def baseEnd_2570024 : Nat := 439885868530252667660227

theorem tailTrace_2570024 : CollatzResearch.WordTrace tailWord_2570024 prefixEnd_2570024 439885868530252667660227 := by
  unfold tailWord_2570024
  simp only [CollatzResearch.WordTrace]
  refine ⟨46868238020624723999846563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62490984027499631999795417 46868238020624723999846563)
  ·
    refine ⟨70302357030937085999769845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46868238020624723999846563 70302357030937085999769845)
    ·
      refine ⟨6590845971650351812478423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70302357030937085999769845 6590845971650351812478423)
      ·
        refine ⟨9886268957475527718717635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6590845971650351812478423 9886268957475527718717635)
        ·
          refine ⟨14829403436213291578076453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9886268957475527718717635 14829403436213291578076453)
          ·
            refine ⟨2780513144289992170889335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14829403436213291578076453 2780513144289992170889335)
            ·
              refine ⟨4170769716434988256334003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2780513144289992170889335 4170769716434988256334003)
              ·
                refine ⟨6256154574652482384501005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4170769716434988256334003 6256154574652482384501005)
                ·
                  refine ⟨2346057965494680894187877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6256154574652482384501005 2346057965494680894187877)
                  ·
                    refine ⟨439885868530252667660227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2346057965494680894187877 439885868530252667660227)
                    ·
                      rfl

theorem cell23_2570024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_2570024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570024 prefixEnd_2570024 := by exact prefixLift 2570024
  have htrace : WordTrace (prefixWord ++ tailWord_2570024) baseStart_2570024 baseEnd_2570024 := by
    simpa [prefixWord, tailWord_2570024, baseEnd_2570024] using wordTrace_append hprefix tailTrace_2570024
  have hstable : (prefixWord ++ tailWord_2570024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570024).length < 2 ^ (prefixWord ++ tailWord_2570024).sum := by decide
  have hdescent : baseEnd_2570024 < baseStart_2570024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570037 : List Nat := [1, 3, 3, 1, 4, 1, 1, 3, 6]
def baseStart_2570037 : Nat := 118140960795 + 2570037 * 2 ^ 59
def prefixEnd_2570037 : Nat := 4983230072969 + 3 ^ 40 * 2570037 * 2
def baseEnd_2570037 : Nat := 146629364537696272457569

theorem tailTrace_2570037 : CollatzResearch.WordTrace tailWord_2570037 prefixEnd_2570037 146629364537696272457569 := by
  unfold tailWord_2570037
  simp only [CollatzResearch.WordTrace]
  refine ⟨93736950190202351219916365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62491300126801567479944243 93736950190202351219916365)
  ·
    refine ⟨35151356321325881707468637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93736950190202351219916365 35151356321325881707468637)
    ·
      refine ⟨13181758620497205640300739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35151356321325881707468637 13181758620497205640300739)
      ·
        refine ⟨19772637930745808460451109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13181758620497205640300739 19772637930745808460451109)
        ·
          refine ⟨3707369612014839086334583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19772637930745808460451109 3707369612014839086334583)
          ·
            refine ⟨5561054418022258629501875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3707369612014839086334583 5561054418022258629501875)
            ·
              refine ⟨8341581627033387944252813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5561054418022258629501875 8341581627033387944252813)
              ·
                refine ⟨3128093110137520479094805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8341581627033387944252813 3128093110137520479094805)
                ·
                  refine ⟨146629364537696272457569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3128093110137520479094805 146629364537696272457569)
                  ·
                    rfl

theorem cell23_2570037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 6].length) (baseStart_2570037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570037 prefixEnd_2570037 := by exact prefixLift 2570037
  have htrace : WordTrace (prefixWord ++ tailWord_2570037) baseStart_2570037 baseEnd_2570037 := by
    simpa [prefixWord, tailWord_2570037, baseEnd_2570037] using wordTrace_append hprefix tailTrace_2570037
  have hstable : (prefixWord ++ tailWord_2570037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570037).length < 2 ^ (prefixWord ++ tailWord_2570037).sum := by decide
  have hdescent : baseEnd_2570037 < baseStart_2570037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570064 : List Nat := [2, 1, 1, 1, 1, 4, 1, 7, 1, 1, 3]
def baseStart_2570064 : Nat := 118140960795 + 2570064 * 2 ^ 59
def prefixEnd_2570064 : Nat := 4983230072969 + 3 ^ 40 * 2570064 * 2
def baseEnd_2570064 : Nat := 1319678144816937846480497

theorem tailTrace_2570064 : CollatzResearch.WordTrace tailWord_2570064 prefixEnd_2570064 1319678144816937846480497 := by
  unfold tailWord_2570064
  simp only [CollatzResearch.WordTrace]
  refine ⟨46868967480552267415574623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62491956640736356554099497 46868967480552267415574623)
  ·
    refine ⟨70303451220828401123361935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46868967480552267415574623 70303451220828401123361935)
    ·
      refine ⟨105455176831242601685042903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70303451220828401123361935 105455176831242601685042903)
      ·
        refine ⟨158182765246863902527564355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105455176831242601685042903 158182765246863902527564355)
        ·
          refine ⟨237274147870295853791346533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158182765246863902527564355 237274147870295853791346533)
          ·
            refine ⟨44488902725680472585877475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 237274147870295853791346533 44488902725680472585877475)
            ·
              refine ⟨66733354088520708878816213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44488902725680472585877475 66733354088520708878816213)
              ·
                refine ⟨1564062986449704114347255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 66733354088520708878816213 1564062986449704114347255)
                ·
                  refine ⟨2346094479674556171520883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1564062986449704114347255 2346094479674556171520883)
                  ·
                    refine ⟨3519141719511834257281325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2346094479674556171520883 3519141719511834257281325)
                    ·
                      refine ⟨1319678144816937846480497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3519141719511834257281325 1319678144816937846480497)
                      ·
                        rfl

theorem cell23_2570064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 7, 1, 1, 3].length) (baseStart_2570064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570064 prefixEnd_2570064 := by exact prefixLift 2570064
  have htrace : WordTrace (prefixWord ++ tailWord_2570064) baseStart_2570064 baseEnd_2570064 := by
    simpa [prefixWord, tailWord_2570064, baseEnd_2570064] using wordTrace_append hprefix tailTrace_2570064
  have hstable : (prefixWord ++ tailWord_2570064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570064).length < 2 ^ (prefixWord ++ tailWord_2570064).sum := by decide
  have hdescent : baseEnd_2570064 < baseStart_2570064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570097 : List Nat := [1, 2, 2, 2, 1, 3, 1, 5, 2, 4]
def baseStart_2570097 : Nat := 118140960795 + 2570097 * 2 ^ 59
def prefixEnd_2570097 : Nat := 4983230072969 + 3 ^ 40 * 2570097 * 2
def baseEnd_2570097 : Nat := 439898363226178739122615

theorem tailTrace_2570097 : CollatzResearch.WordTrace tailWord_2570097 prefixEnd_2570097 439898363226178739122615 := by
  unfold tailWord_2570097
  simp only [CollatzResearch.WordTrace]
  refine ⟨93739138569984981467100545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62492759046656654311400363 93739138569984981467100545)
  ·
    refine ⟨70304353927488736100325409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93739138569984981467100545 70304353927488736100325409)
    ·
      refine ⟨52728265445616552075244057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70304353927488736100325409 52728265445616552075244057)
      ·
        refine ⟨39546199084212414056433043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52728265445616552075244057 39546199084212414056433043)
        ·
          refine ⟨59319298626318621084649565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39546199084212414056433043 59319298626318621084649565)
          ·
            refine ⟨22244736984869482906743587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59319298626318621084649565 22244736984869482906743587)
            ·
              refine ⟨33367105477304224360115381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22244736984869482906743587 33367105477304224360115381)
              ·
                refine ⟨3128166138497271033760817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33367105477304224360115381 3128166138497271033760817)
                ·
                  refine ⟨2346124603872953275320613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3128166138497271033760817 2346124603872953275320613)
                  ·
                    refine ⟨439898363226178739122615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2346124603872953275320613 439898363226178739122615)
                    ·
                      rfl

theorem cell23_2570097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 2, 4].length) (baseStart_2570097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570097 prefixEnd_2570097 := by exact prefixLift 2570097
  have htrace : WordTrace (prefixWord ++ tailWord_2570097) baseStart_2570097 baseEnd_2570097 := by
    simpa [prefixWord, tailWord_2570097, baseEnd_2570097] using wordTrace_append hprefix tailTrace_2570097
  have hstable : (prefixWord ++ tailWord_2570097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570097).length < 2 ^ (prefixWord ++ tailWord_2570097).sum := by decide
  have hdescent : baseEnd_2570097 < baseStart_2570097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570107 : List Nat := [1, 1, 1, 1, 1, 5, 1, 6, 1, 2, 3]
def baseStart_2570107 : Nat := 118140960795 + 2570107 * 2 ^ 59
def prefixEnd_2570107 : Nat := 4983230072969 + 3 ^ 40 * 2570107 * 2
def baseEnd_2570107 : Nat := 1319700224485081178242799

theorem tailTrace_2570107 : CollatzResearch.WordTrace tailWord_2570107 prefixEnd_2570107 1319700224485081178242799 := by
  unfold tailWord_2570107
  simp only [CollatzResearch.WordTrace]
  refine ⟨93739503299948753174964575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62493002199965835449976383 93739503299948753174964575)
  ·
    refine ⟨140609254949923129762446863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93739503299948753174964575 140609254949923129762446863)
    ·
      refine ⟨210913882424884694643670295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140609254949923129762446863 210913882424884694643670295)
      ·
        refine ⟨316370823637327041965505443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210913882424884694643670295 316370823637327041965505443)
        ·
          refine ⟨474556235455990562948258165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316370823637327041965505443 474556235455990562948258165)
          ·
            refine ⟨44489647073999115276399203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 474556235455990562948258165 44489647073999115276399203)
            ·
              refine ⟨66734470610998672914598805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44489647073999115276399203 66734470610998672914598805)
              ·
                refine ⟨3128178309890562792871819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66734470610998672914598805 3128178309890562792871819)
                ·
                  refine ⟨4692267464835844189307729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3128178309890562792871819 4692267464835844189307729)
                  ·
                    refine ⟨3519200598626883141980797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4692267464835844189307729 3519200598626883141980797)
                    ·
                      refine ⟨1319700224485081178242799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3519200598626883141980797 1319700224485081178242799)
                      ·
                        rfl

theorem cell23_2570107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 2, 3].length) (baseStart_2570107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570107 prefixEnd_2570107 := by exact prefixLift 2570107
  have htrace : WordTrace (prefixWord ++ tailWord_2570107) baseStart_2570107 baseEnd_2570107 := by
    simpa [prefixWord, tailWord_2570107, baseEnd_2570107] using wordTrace_append hprefix tailTrace_2570107
  have hstable : (prefixWord ++ tailWord_2570107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570107).length < 2 ^ (prefixWord ++ tailWord_2570107).sum := by decide
  have hdescent : baseEnd_2570107 < baseStart_2570107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570138 : List Nat := [3, 1, 1, 4, 2, 1, 2, 4, 1, 2, 2]
def baseStart_2570138 : Nat := 118140960795 + 2570138 * 2 ^ 59
def prefixEnd_2570138 : Nat := 4983230072969 + 3 ^ 40 * 2570138 * 2
def baseEnd_2570138 : Nat := 1319716142385370556955157

theorem tailTrace_2570138 : CollatzResearch.WordTrace tailWord_2570138 prefixEnd_2570138 1319716142385370556955157 := by
  unfold tailWord_2570138
  simp only [CollatzResearch.WordTrace]
  refine ⟨23435158490709111367335767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62493755975224296979562045 23435158490709111367335767)
  ·
    refine ⟨35152737736063667051003651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23435158490709111367335767 35152737736063667051003651)
    ·
      refine ⟨52729106604095500576505477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35152737736063667051003651 52729106604095500576505477)
      ·
        refine ⟨9886707488267906358094777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52729106604095500576505477 9886707488267906358094777)
        ·
          refine ⟨7415030616200929768571083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9886707488267906358094777 7415030616200929768571083)
          ·
            refine ⟨11122545924301394652856625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7415030616200929768571083 11122545924301394652856625)
            ·
              refine ⟨8341909443226045989642469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11122545924301394652856625 8341909443226045989642469)
              ·
                refine ⟨1564108020604883623057963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8341909443226045989642469 1564108020604883623057963)
                ·
                  refine ⟨2346162030907325434586945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1564108020604883623057963 2346162030907325434586945)
                  ·
                    refine ⟨1759621523180494075940209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2346162030907325434586945 1759621523180494075940209)
                    ·
                      refine ⟨1319716142385370556955157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1759621523180494075940209 1319716142385370556955157)
                      ·
                        rfl

theorem cell23_2570138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_2570138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570138 prefixEnd_2570138 := by exact prefixLift 2570138
  have htrace : WordTrace (prefixWord ++ tailWord_2570138) baseStart_2570138 baseEnd_2570138 := by
    simpa [prefixWord, tailWord_2570138, baseEnd_2570138] using wordTrace_append hprefix tailTrace_2570138
  have hstable : (prefixWord ++ tailWord_2570138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570138).length < 2 ^ (prefixWord ++ tailWord_2570138).sum := by decide
  have hdescent : baseEnd_2570138 < baseStart_2570138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570170 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 4, 6]
def baseStart_2570170 : Nat := 118140960795 + 2570170 * 2 ^ 59
def prefixEnd_2570170 : Nat := 4983230072969 + 3 ^ 40 * 2570170 * 2
def baseEnd_2570170 : Nat := 439910857922104810585003

theorem tailTrace_2570170 : CollatzResearch.WordTrace tailWord_2570170 prefixEnd_2570170 439910857922104810585003 := by
  unfold tailWord_2570170
  simp only [CollatzResearch.WordTrace]
  refine ⟨23435450274680128733626991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62494534065813676623005309 23435450274680128733626991)
  ·
    refine ⟨35153175412020193100440487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23435450274680128733626991 35153175412020193100440487)
    ·
      refine ⟨52729763118030289650660731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35153175412020193100440487 52729763118030289650660731)
      ·
        refine ⟨79094644677045434475991097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52729763118030289650660731 79094644677045434475991097)
        ·
          refine ⟨59320983507784075856993323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79094644677045434475991097 59320983507784075856993323)
          ·
            refine ⟨88981475261676113785489985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59320983507784075856993323 88981475261676113785489985)
            ·
              refine ⟨66736106446257085339117489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88981475261676113785489985 66736106446257085339117489)
              ·
                refine ⟨50052079834692814004338117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66736106446257085339117489 50052079834692814004338117)
                ·
                  refine ⟨9384764969004902625813397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50052079834692814004338117 9384764969004902625813397)
                  ·
                    refine ⟨439910857922104810585003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9384764969004902625813397 439910857922104810585003)
                    ·
                      rfl

theorem cell23_2570170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 4, 6].length) (baseStart_2570170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570170 prefixEnd_2570170 := by exact prefixLift 2570170
  have htrace : WordTrace (prefixWord ++ tailWord_2570170) baseStart_2570170 baseEnd_2570170 := by
    simpa [prefixWord, tailWord_2570170, baseEnd_2570170] using wordTrace_append hprefix tailTrace_2570170
  have hstable : (prefixWord ++ tailWord_2570170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570170).length < 2 ^ (prefixWord ++ tailWord_2570170).sum := by decide
  have hdescent : baseEnd_2570170 < baseStart_2570170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570172 : List Nat := [2, 2, 2, 5, 1, 2, 1, 3, 1, 2, 2]
def baseStart_2570172 : Nat := 118140960795 + 2570172 * 2 ^ 59
def prefixEnd_2570172 : Nat := 4983230072969 + 3 ^ 40 * 2570172 * 2
def baseEnd_2570172 : Nat := 1319733600727623423930001

theorem tailTrace_2570172 : CollatzResearch.WordTrace tailWord_2570172 prefixEnd_2570172 1319733600727623423930001 := by
  unfold tailWord_2570172
  simp only [CollatzResearch.WordTrace]
  refine ⟨46870937022356634638040385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62494582696475512850720513 46870937022356634638040385)
  ·
    refine ⟨35153202766767475978530289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46870937022356634638040385 35153202766767475978530289)
    ·
      refine ⟨26364902075075606983897717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35153202766767475978530289 26364902075075606983897717)
      ·
        refine ⟨2471709569538338154740411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26364902075075606983897717 2471709569538338154740411)
        ·
          refine ⟨3707564354307507232110617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2471709569538338154740411 3707564354307507232110617)
          ·
            refine ⟨2780673265730630424082963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3707564354307507232110617 2780673265730630424082963)
            ·
              refine ⟨4171009898595945636124445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2780673265730630424082963 4171009898595945636124445)
              ·
                refine ⟨1564128711973479613546667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4171009898595945636124445 1564128711973479613546667)
                ·
                  refine ⟨2346193067960219420320001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1564128711973479613546667 2346193067960219420320001)
                  ·
                    refine ⟨1759644800970164565240001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2346193067960219420320001 1759644800970164565240001)
                    ·
                      refine ⟨1319733600727623423930001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1759644800970164565240001 1319733600727623423930001)
                      ·
                        rfl

theorem cell23_2570172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_2570172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570172 prefixEnd_2570172 := by exact prefixLift 2570172
  have htrace : WordTrace (prefixWord ++ tailWord_2570172) baseStart_2570172 baseEnd_2570172 := by
    simpa [prefixWord, tailWord_2570172, baseEnd_2570172] using wordTrace_append hprefix tailTrace_2570172
  have hstable : (prefixWord ++ tailWord_2570172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570172).length < 2 ^ (prefixWord ++ tailWord_2570172).sum := by decide
  have hdescent : baseEnd_2570172 < baseStart_2570172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570205 : List Nat := [1, 4, 3, 1, 3, 2, 2, 1, 2, 1, 3]
def baseStart_2570205 : Nat := 118140960795 + 2570205 * 2 ^ 59
def prefixEnd_2570205 : Nat := 4983230072969 + 3 ^ 40 * 2570205 * 2
def baseEnd_2570205 : Nat := 1319750545589221794817349

theorem tailTrace_2570205 : CollatzResearch.WordTrace tailWord_2570205 prefixEnd_2570205 1319750545589221794817349 := by
  unfold tailWord_2570205
  simp only [CollatzResearch.WordTrace]
  refine ⟨93743077653593715912032069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62495385102395810608021379 93743077653593715912032069)
  ·
    refine ⟨17576827060048821733506013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93743077653593715912032069 17576827060048821733506013)
    ·
      refine ⟨6591310147518308150064755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17576827060048821733506013 6591310147518308150064755)
      ·
        refine ⟨9886965221277462225097133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6591310147518308150064755 9886965221277462225097133)
        ·
          refine ⟨3707611957979048334411425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9886965221277462225097133 3707611957979048334411425)
          ·
            refine ⟨2780708968484286250808569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3707611957979048334411425 2780708968484286250808569)
            ·
              refine ⟨2085531726363214688106427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2780708968484286250808569 2085531726363214688106427)
              ·
                refine ⟨3128297589544822032159641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2085531726363214688106427 3128297589544822032159641)
                ·
                  refine ⟨2346223192158616524119731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3128297589544822032159641 2346223192158616524119731)
                  ·
                    refine ⟨3519334788237924786179597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2346223192158616524119731 3519334788237924786179597)
                    ·
                      refine ⟨1319750545589221794817349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3519334788237924786179597 1319750545589221794817349)
                      ·
                        rfl

theorem cell23_2570205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_2570205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570205 prefixEnd_2570205 := by exact prefixLift 2570205
  have htrace : WordTrace (prefixWord ++ tailWord_2570205) baseStart_2570205 baseEnd_2570205 := by
    simpa [prefixWord, tailWord_2570205, baseEnd_2570205] using wordTrace_append hprefix tailTrace_2570205
  have hstable : (prefixWord ++ tailWord_2570205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570205).length < 2 ^ (prefixWord ++ tailWord_2570205).sum := by decide
  have hdescent : baseEnd_2570205 < baseStart_2570205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570215 : List Nat := [1, 1, 5, 2, 4, 1, 1, 2, 1, 3, 2]
def baseStart_2570215 : Nat := 118140960795 + 2570215 * 2 ^ 59
def prefixEnd_2570215 : Nat := 4983230072969 + 3 ^ 40 * 2570215 * 2
def baseEnd_2570215 : Nat := 1319755680395766755692303

theorem tailTrace_2570215 : CollatzResearch.WordTrace tailWord_2570215 prefixEnd_2570215 1319755680395766755692303 := by
  unfold tailWord_2570215
  simp only [CollatzResearch.WordTrace]
  refine ⟨93743442383557487619896099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62495628255704991746597399 93743442383557487619896099)
  ·
    refine ⟨140615163575336231429844149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93743442383557487619896099 140615163575336231429844149)
    ·
      refine ⟨13182671585187771696547889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 140615163575336231429844149 13182671585187771696547889)
      ·
        refine ⟨9887003688890828772410917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13182671585187771696547889 9887003688890828772410917)
        ·
          refine ⟨1853813191667030394827047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9887003688890828772410917 1853813191667030394827047)
          ·
            refine ⟨2780719787500545592240571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1853813191667030394827047 2780719787500545592240571)
            ·
              refine ⟨4171079681250818388360857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2780719787500545592240571 4171079681250818388360857)
              ·
                refine ⟨3128309760938113791270643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4171079681250818388360857 3128309760938113791270643)
                ·
                  refine ⟨4692464641407170686905965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3128309760938113791270643 4692464641407170686905965)
                  ·
                    refine ⟨1759674240527689007589737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4692464641407170686905965 1759674240527689007589737)
                    ·
                      refine ⟨1319755680395766755692303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1759674240527689007589737 1319755680395766755692303)
                      ·
                        rfl

theorem cell23_2570215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_2570215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570215 prefixEnd_2570215 := by exact prefixLift 2570215
  have htrace : WordTrace (prefixWord ++ tailWord_2570215) baseStart_2570215 baseEnd_2570215 := by
    simpa [prefixWord, tailWord_2570215, baseEnd_2570215] using wordTrace_append hprefix tailTrace_2570215
  have hstable : (prefixWord ++ tailWord_2570215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570215).length < 2 ^ (prefixWord ++ tailWord_2570215).sum := by decide
  have hdescent : baseEnd_2570215 < baseStart_2570215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570220 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 8]
def baseStart_2570220 : Nat := 118140960795 + 2570220 * 2 ^ 59
def prefixEnd_2570220 : Nat := 4983230072969 + 3 ^ 40 * 2570220 * 2
def baseEnd_2570220 : Nat := 1319758247799039236129779

theorem tailTrace_2570220 : CollatzResearch.WordTrace tailWord_2570220 prefixEnd_2570220 1319758247799039236129779 := by
  unfold tailWord_2570220
  simp only [CollatzResearch.WordTrace]
  refine ⟨46871812374269686736914057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62495749832359582315885409 46871812374269686736914057)
  ·
    refine ⟨35153859280702265052685543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46871812374269686736914057 35153859280702265052685543)
    ·
      refine ⟨52730788921053397579028315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35153859280702265052685543 52730788921053397579028315)
      ·
        refine ⟨79096183381580096368542473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52730788921053397579028315 79096183381580096368542473)
        ·
          refine ⟨59322137536185072276406855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79096183381580096368542473 59322137536185072276406855)
          ·
            refine ⟨88983206304277608414610283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59322137536185072276406855 88983206304277608414610283)
            ·
              refine ⟨133474809456416412621915425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88983206304277608414610283 133474809456416412621915425)
              ·
                refine ⟨100106107092312309466436569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133474809456416412621915425 100106107092312309466436569)
                ·
                  refine ⟨75079580319234232099827427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100106107092312309466436569 75079580319234232099827427)
                  ·
                    refine ⟨112619370478851348149741141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75079580319234232099827427 112619370478851348149741141)
                    ·
                      refine ⟨1319758247799039236129779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 112619370478851348149741141 1319758247799039236129779)
                      ·
                        rfl

theorem cell23_2570220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_2570220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570220 prefixEnd_2570220 := by exact prefixLift 2570220
  have htrace : WordTrace (prefixWord ++ tailWord_2570220) baseStart_2570220 baseEnd_2570220 := by
    simpa [prefixWord, tailWord_2570220, baseEnd_2570220] using wordTrace_append hprefix tailTrace_2570220
  have hstable : (prefixWord ++ tailWord_2570220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570220).length < 2 ^ (prefixWord ++ tailWord_2570220).sum := by decide
  have hdescent : baseEnd_2570220 < baseStart_2570220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570254 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2]
def baseStart_2570254 : Nat := 118140960795 + 2570254 * 2 ^ 59
def prefixEnd_2570254 : Nat := 4983230072969 + 3 ^ 40 * 2570254 * 2
def baseEnd_2570254 : Nat := 1319775706141292103104623

theorem tailTrace_2570254 : CollatzResearch.WordTrace tailWord_2570254 prefixEnd_2570254 1319775706141292103104623 := by
  unfold tailWord_2570254
  simp only [CollatzResearch.WordTrace]
  refine ⟨11718108103802024660070727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62496576553610798187043877 11718108103802024660070727)
  ·
    refine ⟨17577162155703036990106091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11718108103802024660070727 17577162155703036990106091)
    ·
      refine ⟨26365743233554555485159137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17577162155703036990106091 26365743233554555485159137)
      ·
        refine ⟨19774307425165916613869353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26365743233554555485159137 19774307425165916613869353)
        ·
          refine ⟨14830730568874437460402015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19774307425165916613869353 14830730568874437460402015)
          ·
            refine ⟨22246095853311656190603023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14830730568874437460402015 22246095853311656190603023)
            ·
              refine ⟨33369143779967484285904535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22246095853311656190603023 33369143779967484285904535)
              ·
                refine ⟨50053715669951226428856803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33369143779967484285904535 50053715669951226428856803)
                ·
                  refine ⟨75080573504926839643285205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50053715669951226428856803 75080573504926839643285205)
                  ·
                    refine ⟨1759700941521722804139497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 75080573504926839643285205 1759700941521722804139497)
                    ·
                      refine ⟨1319775706141292103104623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1759700941521722804139497 1319775706141292103104623)
                      ·
                        rfl

theorem cell23_2570254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_2570254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570254 prefixEnd_2570254 := by exact prefixLift 2570254
  have htrace : WordTrace (prefixWord ++ tailWord_2570254) baseStart_2570254 baseEnd_2570254 := by
    simpa [prefixWord, tailWord_2570254, baseEnd_2570254] using wordTrace_append hprefix tailTrace_2570254
  have hstable : (prefixWord ++ tailWord_2570254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570254).length < 2 ^ (prefixWord ++ tailWord_2570254).sum := by decide
  have hdescent : baseEnd_2570254 < baseStart_2570254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570307 : List Nat := [1, 1, 1, 3, 1, 2, 2, 6, 6]
def baseStart_2570307 : Nat := 118140960795 + 2570307 * 2 ^ 59
def prefixEnd_2570307 : Nat := 4983230072969 + 3 ^ 40 * 2570307 * 2
def baseEnd_2570307 : Nat := 146644768957331155082431

theorem tailTrace_2570307 : CollatzResearch.WordTrace tailWord_2570307 prefixEnd_2570307 146644768957331155082431 := by
  unfold tailWord_2570307
  simp only [CollatzResearch.WordTrace]
  refine ⟨93746797899224187332245175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62497865266149458221496783 93746797899224187332245175)
  ·
    refine ⟨140620196848836280998367763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93746797899224187332245175 140620196848836280998367763)
    ·
      refine ⟨210930295273254421497551645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140620196848836280998367763 210930295273254421497551645)
      ·
        refine ⟨79098860727470408061581867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210930295273254421497551645 79098860727470408061581867)
        ·
          refine ⟨118648291091205612092372801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79098860727470408061581867 118648291091205612092372801)
          ·
            refine ⟨88986218318404209069279601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118648291091205612092372801 88986218318404209069279601)
            ·
              refine ⟨66739663738803156801959701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88986218318404209069279601 66739663738803156801959701)
              ·
                refine ⟨3128421737756397975091861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66739663738803156801959701 3128421737756397975091861)
                ·
                  refine ⟨146644768957331155082431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3128421737756397975091861 146644768957331155082431)
                  ·
                    rfl

theorem cell23_2570307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 6].length) (baseStart_2570307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570307 prefixEnd_2570307 := by exact prefixLift 2570307
  have htrace : WordTrace (prefixWord ++ tailWord_2570307) baseStart_2570307 baseEnd_2570307 := by
    simpa [prefixWord, tailWord_2570307, baseEnd_2570307] using wordTrace_append hprefix tailTrace_2570307
  have hstable : (prefixWord ++ tailWord_2570307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570307).length < 2 ^ (prefixWord ++ tailWord_2570307).sum := by decide
  have hdescent : baseEnd_2570307 < baseStart_2570307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570311 : List Nat := [1, 1, 4, 1, 3, 1, 1, 6, 1, 4]
def baseStart_2570311 : Nat := 118140960795 + 2570311 * 2 ^ 59
def prefixEnd_2570311 : Nat := 4983230072969 + 3 ^ 40 * 2570311 * 2
def baseEnd_2570311 : Nat := 439934991512866126697287

theorem tailTrace_2570311 : CollatzResearch.WordTrace tailWord_2570311 prefixEnd_2570311 439934991512866126697287 := by
  unfold tailWord_2570311
  simp only [CollatzResearch.WordTrace]
  refine ⟨93746943791209696015390787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62497962527473130676927191 93746943791209696015390787)
  ·
    refine ⟨140620415686814544023086181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93746943791209696015390787 140620415686814544023086181)
    ·
      refine ⟨26366327941277727004328659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140620415686814544023086181 26366327941277727004328659)
      ·
        refine ⟨39549491911916590506492989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26366327941277727004328659 39549491911916590506492989)
        ·
          refine ⟨14831059466968721439934871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39549491911916590506492989 14831059466968721439934871)
          ·
            refine ⟨22246589200453082159902307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14831059466968721439934871 22246589200453082159902307)
            ·
              refine ⟨33369883800679623239853461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22246589200453082159902307 33369883800679623239853461)
              ·
                refine ⟨1564213303156857339368131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33369883800679623239853461 1564213303156857339368131)
                ·
                  refine ⟨2346319954735286009052197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1564213303156857339368131 2346319954735286009052197)
                  ·
                    refine ⟨439934991512866126697287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2346319954735286009052197 439934991512866126697287)
                    ·
                      rfl

theorem cell23_2570311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 6, 1, 4].length) (baseStart_2570311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570311 prefixEnd_2570311 := by exact prefixLift 2570311
  have htrace : WordTrace (prefixWord ++ tailWord_2570311) baseStart_2570311 baseEnd_2570311 := by
    simpa [prefixWord, tailWord_2570311, baseEnd_2570311] using wordTrace_append hprefix tailTrace_2570311
  have hstable : (prefixWord ++ tailWord_2570311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570311).length < 2 ^ (prefixWord ++ tailWord_2570311).sum := by decide
  have hdescent : baseEnd_2570311 < baseStart_2570311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570361 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 4, 3, 2]
def baseStart_2570361 : Nat := 118140960795 + 2570361 * 2 ^ 59
def prefixEnd_2570361 : Nat := 4983230072969 + 3 ^ 40 * 2570361 * 2
def baseEnd_2570361 : Nat := 1319830648571323184466631

theorem tailTrace_2570361 : CollatzResearch.WordTrace tailWord_2570361 prefixEnd_2570361 1319830648571323184466631 := by
  unfold tailWord_2570361
  simp only [CollatzResearch.WordTrace]
  refine ⟨93748767441028554554710937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62499178294019036369807291 93748767441028554554710937)
  ·
    refine ⟨70311575580771415916033203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93748767441028554554710937 70311575580771415916033203)
    ·
      refine ⟨105467363371157123874049805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70311575580771415916033203 105467363371157123874049805)
      ·
        refine ⟨39550261264183921452768677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105467363371157123874049805 39550261264183921452768677)
        ·
          refine ⟨7415673987034485272394127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39550261264183921452768677 7415673987034485272394127)
          ·
            refine ⟨11123510980551727908591191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7415673987034485272394127 11123510980551727908591191)
            ·
              refine ⟨16685266470827591862886787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11123510980551727908591191 16685266470827591862886787)
              ·
                refine ⟨25027899706241387794330181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16685266470827591862886787 25027899706241387794330181)
                ·
                  refine ⟨4692731194920260211436909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25027899706241387794330181 4692731194920260211436909)
                  ·
                    refine ⟨1759774198095097579288841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4692731194920260211436909 1759774198095097579288841)
                    ·
                      refine ⟨1319830648571323184466631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1759774198095097579288841 1319830648571323184466631)
                      ·
                        rfl

theorem cell23_2570361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 3, 2].length) (baseStart_2570361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570361 prefixEnd_2570361 := by exact prefixLift 2570361
  have htrace : WordTrace (prefixWord ++ tailWord_2570361) baseStart_2570361 baseEnd_2570361 := by
    simpa [prefixWord, tailWord_2570361, baseEnd_2570361] using wordTrace_append hprefix tailTrace_2570361
  have hstable : (prefixWord ++ tailWord_2570361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570361).length < 2 ^ (prefixWord ++ tailWord_2570361).sum := by decide
  have hdescent : baseEnd_2570361 < baseStart_2570361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570388 : List Nat := [2, 4, 2, 3, 1, 1, 1, 1, 3, 5]
def baseStart_2570388 : Nat := 118140960795 + 2570388 * 2 ^ 59
def prefixEnd_2570388 : Nat := 4983230072969 + 3 ^ 40 * 2570388 * 2
def baseEnd_2570388 : Nat := 439948170849664859609669

theorem tailTrace_2570388 : CollatzResearch.WordTrace tailWord_2570388 prefixEnd_2570388 439948170849664859609669 := by
  unfold tailWord_2570388
  simp only [CollatzResearch.WordTrace]
  refine ⟨46874876105965369082971909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62499834807953825443962545 46874876105965369082971909)
  ·
    refine ⟨8789039269868506703057233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46874876105965369082971909 8789039269868506703057233)
    ·
      refine ⟨6591779452401380027292925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8789039269868506703057233 6591779452401380027292925)
      ·
        refine ⟨2471917294650517510234847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6591779452401380027292925 2471917294650517510234847)
        ·
          refine ⟨3707875941975776265352271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2471917294650517510234847 3707875941975776265352271)
          ·
            refine ⟨5561813912963664398028407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3707875941975776265352271 5561813912963664398028407)
            ·
              refine ⟨8342720869445496597042611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5561813912963664398028407 8342720869445496597042611)
              ·
                refine ⟨12514081304168244895563917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8342720869445496597042611 12514081304168244895563917)
                ·
                  refine ⟨4692780489063091835836469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12514081304168244895563917 4692780489063091835836469)
                  ·
                    refine ⟨439948170849664859609669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4692780489063091835836469 439948170849664859609669)
                    ·
                      rfl

theorem cell23_2570388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_2570388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570388 prefixEnd_2570388 := by exact prefixLift 2570388
  have htrace : WordTrace (prefixWord ++ tailWord_2570388) baseStart_2570388 baseEnd_2570388 := by
    simpa [prefixWord, tailWord_2570388, baseEnd_2570388] using wordTrace_append hprefix tailTrace_2570388
  have hstable : (prefixWord ++ tailWord_2570388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570388).length < 2 ^ (prefixWord ++ tailWord_2570388).sum := by decide
  have hdescent : baseEnd_2570388 < baseStart_2570388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570391 : List Nat := [1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 4]
def baseStart_2570391 : Nat := 118140960795 + 2570391 * 2 ^ 59
def prefixEnd_2570391 : Nat := 4983230072969 + 3 ^ 40 * 2570391 * 2
def baseEnd_2570391 : Nat := 1319846052990958067091493

theorem tailTrace_2570391 : CollatzResearch.WordTrace tailWord_2570391 prefixEnd_2570391 1319846052990958067091493 := by
  unfold tailWord_2570391
  simp only [CollatzResearch.WordTrace]
  refine ⟨93749861630919869678303027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62499907753946579785535351 93749861630919869678303027)
  ·
    refine ⟨140624792446379804517454541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93749861630919869678303027 140624792446379804517454541)
    ·
      refine ⟨52734297167392426694045453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140624792446379804517454541 52734297167392426694045453)
      ·
        refine ⟨19775361437772160010267045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52734297167392426694045453 19775361437772160010267045)
        ·
          refine ⟨3707880269582280001925071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19775361437772160010267045 3707880269582280001925071)
          ·
            refine ⟨5561820404373420002887607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3707880269582280001925071 5561820404373420002887607)
            ·
              refine ⟨8342730606560130004331411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5561820404373420002887607 8342730606560130004331411)
              ·
                refine ⟨12514095909840195006497117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8342730606560130004331411 12514095909840195006497117)
                ·
                  refine ⟨4692785966190073127436419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12514095909840195006497117 4692785966190073127436419)
                  ·
                    refine ⟨7039178949285109691154629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4692785966190073127436419 7039178949285109691154629)
                    ·
                      refine ⟨1319846052990958067091493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7039178949285109691154629 1319846052990958067091493)
                      ·
                        rfl

theorem cell23_2570391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_2570391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570391 prefixEnd_2570391 := by exact prefixLift 2570391
  have htrace : WordTrace (prefixWord ++ tailWord_2570391) baseStart_2570391 baseEnd_2570391 := by
    simpa [prefixWord, tailWord_2570391, baseEnd_2570391] using wordTrace_append hprefix tailTrace_2570391
  have hstable : (prefixWord ++ tailWord_2570391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570391).length < 2 ^ (prefixWord ++ tailWord_2570391).sum := by decide
  have hdescent : baseEnd_2570391 < baseStart_2570391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570424 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 3, 3, 3]
def baseStart_2570424 : Nat := 118140960795 + 2570424 * 2 ^ 59
def prefixEnd_2570424 : Nat := 4983230072969 + 3 ^ 40 * 2570424 * 2
def baseEnd_2570424 : Nat := 1319862997852556437978841

theorem tailTrace_2570424 : CollatzResearch.WordTrace tailWord_2570424 prefixEnd_2570424 1319862997852556437978841 := by
  unfold tailWord_2570424
  simp only [CollatzResearch.WordTrace]
  refine ⟨46875532619900158157127163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62500710159866877542836217 46875532619900158157127163)
  ·
    refine ⟨70313298929850237235690745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46875532619900158157127163 70313298929850237235690745)
    ·
      refine ⟨52734974197387677926768059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70313298929850237235690745 52734974197387677926768059)
      ·
        refine ⟨79102461296081516890152089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52734974197387677926768059 79102461296081516890152089)
        ·
          refine ⟨59326845972061137667614067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79102461296081516890152089 59326845972061137667614067)
          ·
            refine ⟨88990268958091706501421101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59326845972061137667614067 88990268958091706501421101)
            ·
              refine ⟨33371350859284389938032913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88990268958091706501421101 33371350859284389938032913)
              ·
                refine ⟨25028513144463292453524685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33371350859284389938032913 25028513144463292453524685)
                ·
                  refine ⟨9385692429173734670071757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25028513144463292453524685 9385692429173734670071757)
                  ·
                    refine ⟨3519634660940150501276909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9385692429173734670071757 3519634660940150501276909)
                    ·
                      refine ⟨1319862997852556437978841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3519634660940150501276909 1319862997852556437978841)
                      ·
                        rfl

theorem cell23_2570424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 3, 3, 3].length) (baseStart_2570424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570424 prefixEnd_2570424 := by exact prefixLift 2570424
  have htrace : WordTrace (prefixWord ++ tailWord_2570424) baseStart_2570424 baseEnd_2570424 := by
    simpa [prefixWord, tailWord_2570424, baseEnd_2570424] using wordTrace_append hprefix tailTrace_2570424
  have hstable : (prefixWord ++ tailWord_2570424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570424).length < 2 ^ (prefixWord ++ tailWord_2570424).sum := by decide
  have hdescent : baseEnd_2570424 < baseStart_2570424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570425 : List Nat := [1, 2, 1, 4, 1, 2, 3, 4, 1, 2, 2]
def baseStart_2570425 : Nat := 118140960795 + 2570425 * 2 ^ 59
def prefixEnd_2570425 : Nat := 4983230072969 + 3 ^ 40 * 2570425 * 2
def baseEnd_2570425 : Nat := 1319863511333210934066337

theorem tailTrace_2570425 : CollatzResearch.WordTrace tailWord_2570425 prefixEnd_2570425 1319863511333210934066337 := by
  unfold tailWord_2570425
  simp only [CollatzResearch.WordTrace]
  refine ⟨93751101712796693485040729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62500734475197795656693819 93751101712796693485040729)
  ·
    refine ⟨70313326284597520113780547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93751101712796693485040729 70313326284597520113780547)
    ·
      refine ⟨105469989426896280170670821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70313326284597520113780547 105469989426896280170670821)
      ·
        refine ⟨19775623017543052532000779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105469989426896280170670821 19775623017543052532000779)
        ·
          refine ⟨29663434526314578798001169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19775623017543052532000779 29663434526314578798001169)
          ·
            refine ⟨22247575894735934098500877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29663434526314578798001169 22247575894735934098500877)
            ·
              refine ⟨8342840960525975286937829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22247575894735934098500877 8342840960525975286937829)
              ·
                refine ⟨1564282680098620366300843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8342840960525975286937829 1564282680098620366300843)
                ·
                  refine ⟨2346424020147930549451265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1564282680098620366300843 2346424020147930549451265)
                  ·
                    refine ⟨1759818015110947912088449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2346424020147930549451265 1759818015110947912088449)
                    ·
                      refine ⟨1319863511333210934066337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1759818015110947912088449 1319863511333210934066337)
                      ·
                        rfl

theorem cell23_2570425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_2570425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570425 prefixEnd_2570425 := by exact prefixLift 2570425
  have htrace : WordTrace (prefixWord ++ tailWord_2570425) baseStart_2570425 baseEnd_2570425 := by
    simpa [prefixWord, tailWord_2570425, baseEnd_2570425] using wordTrace_append hprefix tailTrace_2570425
  have hstable : (prefixWord ++ tailWord_2570425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570425).length < 2 ^ (prefixWord ++ tailWord_2570425).sum := by decide
  have hdescent : baseEnd_2570425 < baseStart_2570425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570427 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 1, 9]
def baseStart_2570427 : Nat := 118140960795 + 2570427 * 2 ^ 59
def prefixEnd_2570427 : Nat := 4983230072969 + 3 ^ 40 * 2570427 * 2
def baseEnd_2570427 : Nat := 439954846098173308747109

theorem tailTrace_2570427 : CollatzResearch.WordTrace tailWord_2570427 prefixEnd_2570427 439954846098173308747109 := by
  unfold tailWord_2570427
  simp only [CollatzResearch.WordTrace]
  refine ⟨93751174658789447826613535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62500783105859631884409023 93751174658789447826613535)
  ·
    refine ⟨140626761988184171739920303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93751174658789447826613535 140626761988184171739920303)
    ·
      refine ⟨210940142982276257609880455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140626761988184171739920303 210940142982276257609880455)
      ·
        refine ⟨316410214473414386414820683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210940142982276257609880455 316410214473414386414820683)
        ·
          refine ⟨474615321710121579622231025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316410214473414386414820683 474615321710121579622231025)
          ·
            refine ⟨355961491282591184716673269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 474615321710121579622231025 355961491282591184716673269)
            ·
              refine ⟨33371389807742923567188119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 355961491282591184716673269 33371389807742923567188119)
              ·
                refine ⟨50057084711614385350782179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33371389807742923567188119 50057084711614385350782179)
                ·
                  refine ⟨75085627067421578026173269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50057084711614385350782179 75085627067421578026173269)
                  ·
                    refine ⟨439954846098173308747109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 75085627067421578026173269 439954846098173308747109)
                    ·
                      rfl

theorem cell23_2570427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 9].length) (baseStart_2570427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570427 prefixEnd_2570427 := by exact prefixLift 2570427
  have htrace : WordTrace (prefixWord ++ tailWord_2570427) baseStart_2570427 baseEnd_2570427 := by
    simpa [prefixWord, tailWord_2570427, baseEnd_2570427] using wordTrace_append hprefix tailTrace_2570427
  have hstable : (prefixWord ++ tailWord_2570427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570427).length < 2 ^ (prefixWord ++ tailWord_2570427).sum := by decide
  have hdescent : baseEnd_2570427 < baseStart_2570427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570474 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 4, 6]
def baseStart_2570474 : Nat := 118140960795 + 2570474 * 2 ^ 59
def prefixEnd_2570474 : Nat := 4983230072969 + 3 ^ 40 * 2570474 * 2
def baseEnd_2570474 : Nat := 439962890628427080784537

theorem tailTrace_2570474 : CollatzResearch.WordTrace tailWord_2570474 prefixEnd_2570474 439962890628427080784537 := by
  unfold tailWord_2570474
  simp only [CollatzResearch.WordTrace]
  refine ⟨23438222222404793713393619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62501925926412783235716317 23438222222404793713393619)
  ·
    refine ⟨35157333333607190570090429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23438222222404793713393619 35157333333607190570090429)
    ·
      refine ⟨13184000000102696463783911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35157333333607190570090429 13184000000102696463783911)
      ·
        refine ⟨19776000000154044695675867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13184000000102696463783911 19776000000154044695675867)
        ·
          refine ⟨29664000000231067043513801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19776000000154044695675867 29664000000231067043513801)
          ·
            refine ⟨22248000000173300282635351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29664000000231067043513801 22248000000173300282635351)
            ·
              refine ⟨33372000000259950423953027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22248000000173300282635351 33372000000259950423953027)
              ·
                refine ⟨50058000000389925635929541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33372000000259950423953027 50058000000389925635929541)
                ·
                  refine ⟨9385875000073111056736789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50058000000389925635929541 9385875000073111056736789)
                  ·
                    refine ⟨439962890628427080784537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9385875000073111056736789 439962890628427080784537)
                    ·
                      rfl

theorem cell23_2570474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_2570474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570474 prefixEnd_2570474 := by exact prefixLift 2570474
  have htrace : WordTrace (prefixWord ++ tailWord_2570474) baseStart_2570474 baseEnd_2570474 := by
    simpa [prefixWord, tailWord_2570474, baseEnd_2570474] using wordTrace_append hprefix tailTrace_2570474
  have hstable : (prefixWord ++ tailWord_2570474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570474).length < 2 ^ (prefixWord ++ tailWord_2570474).sum := by decide
  have hdescent : baseEnd_2570474 < baseStart_2570474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570481 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 3, 4, 2]
def baseStart_2570481 : Nat := 118140960795 + 2570481 * 2 ^ 59
def prefixEnd_2570481 : Nat := 4983230072969 + 3 ^ 40 * 2570481 * 2
def baseEnd_2570481 : Nat := 1319892266249862714966079

theorem tailTrace_2570481 : CollatzResearch.WordTrace tailWord_2570481 prefixEnd_2570481 1319892266249862714966079 := by
  unfold tailWord_2570481
  simp only [CollatzResearch.WordTrace]
  refine ⟨93753144200593815049079297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62502096133729210032719531 93753144200593815049079297)
  ·
    refine ⟨70314858150445361286809473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93753144200593815049079297 70314858150445361286809473)
    ·
      refine ⟨52736143612834020965107105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70314858150445361286809473 52736143612834020965107105)
      ·
        refine ⟨39552107709625515723830329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52736143612834020965107105 39552107709625515723830329)
        ·
          refine ⟨29664080782219136792872747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39552107709625515723830329 29664080782219136792872747)
          ·
            refine ⟨44496121173328705189309121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29664080782219136792872747 44496121173328705189309121)
            ·
              refine ⟨33372090879996528891981841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44496121173328705189309121 33372090879996528891981841)
              ·
                refine ⟨25029068159997396668986381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33372090879996528891981841 25029068159997396668986381)
                ·
                  refine ⟨9385900559999023750869893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25029068159997396668986381 9385900559999023750869893)
                  ·
                    refine ⟨1759856354999816953288105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9385900559999023750869893 1759856354999816953288105)
                    ·
                      refine ⟨1319892266249862714966079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1759856354999816953288105 1319892266249862714966079)
                      ·
                        rfl

theorem cell23_2570481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 4, 2].length) (baseStart_2570481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570481 prefixEnd_2570481 := by exact prefixLift 2570481
  have htrace : WordTrace (prefixWord ++ tailWord_2570481) baseStart_2570481 baseEnd_2570481 := by
    simpa [prefixWord, tailWord_2570481, baseEnd_2570481] using wordTrace_append hprefix tailTrace_2570481
  have hstable : (prefixWord ++ tailWord_2570481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570481).length < 2 ^ (prefixWord ++ tailWord_2570481).sum := by decide
  have hdescent : baseEnd_2570481 < baseStart_2570481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570571 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 3, 6, 2]
def baseStart_2570571 : Nat := 118140960795 + 2570571 * 2 ^ 59
def prefixEnd_2570571 : Nat := 4983230072969 + 3 ^ 40 * 2570571 * 2
def baseEnd_2570571 : Nat := 1319938479508767362840665

theorem tailTrace_2570571 : CollatzResearch.WordTrace tailWord_2570571 prefixEnd_2570571 1319938479508767362840665 := by
  unfold tailWord_2570571
  simp only [CollatzResearch.WordTrace]
  refine ⟨93756426770267760419855567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62504284513511840279903711 93756426770267760419855567)
  ·
    refine ⟨140634640155401640629783351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93756426770267760419855567 140634640155401640629783351)
    ·
      refine ⟨210951960233102460944675027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140634640155401640629783351 210951960233102460944675027)
      ·
        refine ⟨316427940349653691417012541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210951960233102460944675027 316427940349653691417012541)
        ·
          refine ⟨118660477631120134281379703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 316427940349653691417012541 118660477631120134281379703)
          ·
            refine ⟨177990716446680201422069555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118660477631120134281379703 177990716446680201422069555)
            ·
              refine ⟨266986074670020302133104333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177990716446680201422069555 266986074670020302133104333)
              ·
                refine ⟨100119778001257613299914125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 266986074670020302133104333 100119778001257613299914125)
                ·
                  refine ⟨37544916750471604987467797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100119778001257613299914125 37544916750471604987467797)
                  ·
                    refine ⟨1759917972678356483787553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37544916750471604987467797 1759917972678356483787553)
                    ·
                      refine ⟨1319938479508767362840665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1759917972678356483787553 1319938479508767362840665)
                      ·
                        rfl

theorem cell23_2570571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 6, 2].length) (baseStart_2570571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570571 prefixEnd_2570571 := by exact prefixLift 2570571
  have htrace : WordTrace (prefixWord ++ tailWord_2570571) baseStart_2570571 baseEnd_2570571 := by
    simpa [prefixWord, tailWord_2570571, baseEnd_2570571] using wordTrace_append hprefix tailTrace_2570571
  have hstable : (prefixWord ++ tailWord_2570571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570571).length < 2 ^ (prefixWord ++ tailWord_2570571).sum := by decide
  have hdescent : baseEnd_2570571 < baseStart_2570571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570625 : List Nat := [1, 2, 4, 3, 1, 1, 3, 1, 2, 2, 3]
def baseStart_2570625 : Nat := 118140960795 + 2570625 * 2 ^ 59
def prefixEnd_2570625 : Nat := 4983230072969 + 3 ^ 40 * 2570625 * 2
def baseEnd_2570625 : Nat := 1319966207464110151565417

theorem tailTrace_2570625 : CollatzResearch.WordTrace tailWord_2570625 prefixEnd_2570625 1319966207464110151565417 := by
  unfold tailWord_2570625
  simp only [CollatzResearch.WordTrace]
  refine ⟨93758396312072127642321329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62505597541381418428214219 93758396312072127642321329)
  ·
    refine ⟨70318797234054095731740997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93758396312072127642321329 70318797234054095731740997)
    ·
      refine ⟨13184774481385142949701437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70318797234054095731740997 13184774481385142949701437)
      ·
        refine ⟨4944290430519428606138039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13184774481385142949701437 4944290430519428606138039)
        ·
          refine ⟨7416435645779142909207059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4944290430519428606138039 7416435645779142909207059)
          ·
            refine ⟨11124653468668714363810589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7416435645779142909207059 11124653468668714363810589)
            ·
              refine ⟨4171745050750767886428971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11124653468668714363810589 4171745050750767886428971)
              ·
                refine ⟨6257617576126151829643457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4171745050750767886428971 6257617576126151829643457)
                ·
                  refine ⟨4693213182094613872232593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6257617576126151829643457 4693213182094613872232593)
                  ·
                    refine ⟨3519909886570960404174445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4693213182094613872232593 3519909886570960404174445)
                    ·
                      refine ⟨1319966207464110151565417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3519909886570960404174445 1319966207464110151565417)
                      ·
                        rfl

theorem cell23_2570625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_2570625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570625 prefixEnd_2570625 := by exact prefixLift 2570625
  have htrace : WordTrace (prefixWord ++ tailWord_2570625) baseStart_2570625 baseEnd_2570625 := by
    simpa [prefixWord, tailWord_2570625, baseEnd_2570625] using wordTrace_append hprefix tailTrace_2570625
  have hstable : (prefixWord ++ tailWord_2570625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570625).length < 2 ^ (prefixWord ++ tailWord_2570625).sum := by decide
  have hdescent : baseEnd_2570625 < baseStart_2570625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570655 : List Nat := [1, 1, 2, 5, 1, 1, 4, 1, 3, 1, 3]
def baseStart_2570655 : Nat := 118140960795 + 2570655 * 2 ^ 59
def prefixEnd_2570655 : Nat := 4983230072969 + 3 ^ 40 * 2570655 * 2
def baseEnd_2570655 : Nat := 1319981611883745034190279

theorem tailTrace_2570655 : CollatzResearch.WordTrace tailWord_2570655 prefixEnd_2570655 1319981611883745034190279 := by
  unfold tailWord_2570655
  simp only [CollatzResearch.WordTrace]
  refine ⟨93759490501963442765913419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62506327001308961843942279 93759490501963442765913419)
  ·
    refine ⟨140639235752945164148870129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93759490501963442765913419 140639235752945164148870129)
    ·
      refine ⟨105479426814708873111652597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140639235752945164148870129 105479426814708873111652597)
      ·
        refine ⟨9888696263878956854217431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105479426814708873111652597 9888696263878956854217431)
        ·
          refine ⟨14833044395818435281326147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9888696263878956854217431 14833044395818435281326147)
          ·
            refine ⟨22249566593727652921989221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14833044395818435281326147 22249566593727652921989221)
            ·
              refine ⟨4171793736323934922872979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22249566593727652921989221 4171793736323934922872979)
              ·
                refine ⟨6257690604485902384309469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4171793736323934922872979 6257690604485902384309469)
                ·
                  refine ⟨2346633976682213394116051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6257690604485902384309469 2346633976682213394116051)
                  ·
                    refine ⟨3519950965023320091174077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2346633976682213394116051 3519950965023320091174077)
                    ·
                      refine ⟨1319981611883745034190279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3519950965023320091174077 1319981611883745034190279)
                      ·
                        rfl

theorem cell23_2570655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_2570655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570655 prefixEnd_2570655 := by exact prefixLift 2570655
  have htrace : WordTrace (prefixWord ++ tailWord_2570655) baseStart_2570655 baseEnd_2570655 := by
    simpa [prefixWord, tailWord_2570655, baseEnd_2570655] using wordTrace_append hprefix tailTrace_2570655
  have hstable : (prefixWord ++ tailWord_2570655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570655).length < 2 ^ (prefixWord ++ tailWord_2570655).sum := by decide
  have hdescent : baseEnd_2570655 < baseStart_2570655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570691 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 4]
def baseStart_2570691 : Nat := 118140960795 + 2570691 * 2 ^ 59
def prefixEnd_2570691 : Nat := 4983230072969 + 3 ^ 40 * 2570691 * 2
def baseEnd_2570691 : Nat := 1320000097187306893340113

theorem tailTrace_2570691 : CollatzResearch.WordTrace tailWord_2570691 prefixEnd_2570691 1320000097187306893340113 := by
  unfold tailWord_2570691
  simp only [CollatzResearch.WordTrace]
  refine ⟨93760803529833020914223927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62507202353222013942815951 93760803529833020914223927)
  ·
    refine ⟨140641205294749531371335891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93760803529833020914223927 140641205294749531371335891)
    ·
      refine ⟨210961807942124297057003837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140641205294749531371335891 210961807942124297057003837)
      ·
        refine ⟨79110677978296611396376439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210961807942124297057003837 79110677978296611396376439)
        ·
          refine ⟨118666016967444917094564659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79110677978296611396376439 118666016967444917094564659)
          ·
            refine ⟨177999025451167375641846989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118666016967444917094564659 177999025451167375641846989)
            ·
              refine ⟨66749634544187765865692621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177999025451167375641846989 66749634544187765865692621)
              ·
                refine ⟨25031112954070412199634733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66749634544187765865692621 25031112954070412199634733)
                ·
                  refine ⟨9386667357776404574863025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25031112954070412199634733 9386667357776404574863025)
                  ·
                    refine ⟨7040000518332303431147269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9386667357776404574863025 7040000518332303431147269)
                    ·
                      refine ⟨1320000097187306893340113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7040000518332303431147269 1320000097187306893340113)
                      ·
                        rfl

theorem cell23_2570691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_2570691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570691 prefixEnd_2570691 := by exact prefixLift 2570691
  have htrace : WordTrace (prefixWord ++ tailWord_2570691) baseStart_2570691 baseEnd_2570691 := by
    simpa [prefixWord, tailWord_2570691, baseEnd_2570691] using wordTrace_append hprefix tailTrace_2570691
  have hstable : (prefixWord ++ tailWord_2570691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570691).length < 2 ^ (prefixWord ++ tailWord_2570691).sum := by decide
  have hdescent : baseEnd_2570691 < baseStart_2570691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570698 : List Nat := [3, 1, 2, 1, 2, 2, 4, 1, 1, 1, 5]
def baseStart_2570698 : Nat := 118140960795 + 2570698 * 2 ^ 59
def prefixEnd_2570698 : Nat := 4983230072969 + 3 ^ 40 * 2570698 * 2
def baseEnd_2570698 : Nat := 1320003691551888365952581

theorem tailTrace_2570698 : CollatzResearch.WordTrace tailWord_2570698 prefixEnd_2570698 1320003691551888365952581 := by
  unfold tailWord_2570698
  simp only [CollatzResearch.WordTrace]
  refine ⟨23440264710201915277432187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62507372560538440739819165 23440264710201915277432187)
  ·
    refine ⟨35160397065302872916148281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23440264710201915277432187 35160397065302872916148281)
    ·
      refine ⟨26370297798977154687111211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35160397065302872916148281 26370297798977154687111211)
      ·
        refine ⟨39555446698465732030666817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26370297798977154687111211 39555446698465732030666817)
        ·
          refine ⟨29666585023849299023000113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39555446698465732030666817 29666585023849299023000113)
          ·
            refine ⟨22249938767886974267250085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29666585023849299023000113 22249938767886974267250085)
            ·
              refine ⟨4171863518978807675109391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22249938767886974267250085 4171863518978807675109391)
              ·
                refine ⟨6257795278468211512664087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4171863518978807675109391 6257795278468211512664087)
                ·
                  refine ⟨9386692917702317268996131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6257795278468211512664087 9386692917702317268996131)
                  ·
                    refine ⟨14080039376553475903494197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9386692917702317268996131 14080039376553475903494197)
                    ·
                      refine ⟨1320003691551888365952581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14080039376553475903494197 1320003691551888365952581)
                      ·
                        rfl

theorem cell23_2570698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_2570698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570698 prefixEnd_2570698 := by exact prefixLift 2570698
  have htrace : WordTrace (prefixWord ++ tailWord_2570698) baseStart_2570698 baseEnd_2570698 := by
    simpa [prefixWord, tailWord_2570698, baseEnd_2570698] using wordTrace_append hprefix tailTrace_2570698
  have hstable : (prefixWord ++ tailWord_2570698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570698).length < 2 ^ (prefixWord ++ tailWord_2570698).sum := by decide
  have hdescent : baseEnd_2570698 < baseStart_2570698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570706 : List Nat := [3, 2, 2, 4, 2, 1, 1, 1, 3, 1, 3]
def baseStart_2570706 : Nat := 118140960795 + 2570706 * 2 ^ 59
def prefixEnd_2570706 : Nat := 4983230072969 + 3 ^ 40 * 2570706 * 2
def baseEnd_2570706 : Nat := 1320007799397124334652545

theorem tailTrace_2570706 : CollatzResearch.WordTrace tailWord_2570706 prefixEnd_2570706 1320007799397124334652545 := by
  unfold tailWord_2570706
  simp only [CollatzResearch.WordTrace]
  refine ⟨23440337656194669619004993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62507567083185785650679981 23440337656194669619004993)
  ·
    refine ⟨17580253242146002214253745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23440337656194669619004993 17580253242146002214253745)
    ·
      refine ⟨13185189931609501660690309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17580253242146002214253745 13185189931609501660690309)
      ·
        refine ⟨2472223112176781561379433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13185189931609501660690309 2472223112176781561379433)
        ·
          refine ⟨1854167334132586171034575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2472223112176781561379433 1854167334132586171034575)
          ·
            refine ⟨2781251001198879256551863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1854167334132586171034575 2781251001198879256551863)
            ·
              refine ⟨4171876501798318884827795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2781251001198879256551863 4171876501798318884827795)
              ·
                refine ⟨6257814752697478327241693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4171876501798318884827795 6257814752697478327241693)
                ·
                  refine ⟨2346680532261554372715635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6257814752697478327241693 2346680532261554372715635)
                  ·
                    refine ⟨3520020798392331559073453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2346680532261554372715635 3520020798392331559073453)
                    ·
                      refine ⟨1320007799397124334652545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3520020798392331559073453 1320007799397124334652545)
                      ·
                        rfl

theorem cell23_2570706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_2570706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570706 prefixEnd_2570706 := by exact prefixLift 2570706
  have htrace : WordTrace (prefixWord ++ tailWord_2570706) baseStart_2570706 baseEnd_2570706 := by
    simpa [prefixWord, tailWord_2570706, baseEnd_2570706] using wordTrace_append hprefix tailTrace_2570706
  have hstable : (prefixWord ++ tailWord_2570706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570706).length < 2 ^ (prefixWord ++ tailWord_2570706).sum := by decide
  have hdescent : baseEnd_2570706 < baseStart_2570706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570708 : List Nat := [2, 4, 1, 2, 2, 1, 1, 2, 1, 1, 6]
def baseStart_2570708 : Nat := 118140960795 + 2570708 * 2 ^ 59
def prefixEnd_2570708 : Nat := 4983230072969 + 3 ^ 40 * 2570708 * 2
def baseEnd_2570708 : Nat := 1320008826358433326827535

theorem tailTrace_2570708 : CollatzResearch.WordTrace tailWord_2570708 prefixEnd_2570708 1320008826358433326827535 := by
  unfold tailWord_2570708
  simp only [CollatzResearch.WordTrace]
  refine ⟨46880711785385716408796389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62507615713847621878395185 46880711785385716408796389)
  ·
    refine ⟨8790133459759821826649323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46880711785385716408796389 8790133459759821826649323)
    ·
      refine ⟨13185200189639732739973985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8790133459759821826649323 13185200189639732739973985)
      ·
        refine ⟨9888900142229799554980489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13185200189639732739973985 9888900142229799554980489)
        ·
          refine ⟨7416675106672349666235367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9888900142229799554980489 7416675106672349666235367)
          ·
            refine ⟨11125012660008524499353051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7416675106672349666235367 11125012660008524499353051)
            ·
              refine ⟨16687518990012786749029577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11125012660008524499353051 16687518990012786749029577)
              ·
                refine ⟨12515639242509590061772183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16687518990012786749029577 12515639242509590061772183)
                ·
                  refine ⟨18773458863764385092658275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12515639242509590061772183 18773458863764385092658275)
                  ·
                    refine ⟨28160188295646577638987413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18773458863764385092658275 28160188295646577638987413)
                    ·
                      refine ⟨1320008826358433326827535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28160188295646577638987413 1320008826358433326827535)
                      ·
                        rfl

theorem cell23_2570708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_2570708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570708 prefixEnd_2570708 := by exact prefixLift 2570708
  have htrace : WordTrace (prefixWord ++ tailWord_2570708) baseStart_2570708 baseEnd_2570708 := by
    simpa [prefixWord, tailWord_2570708, baseEnd_2570708] using wordTrace_append hprefix tailTrace_2570708
  have hstable : (prefixWord ++ tailWord_2570708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570708).length < 2 ^ (prefixWord ++ tailWord_2570708).sum := by decide
  have hdescent : baseEnd_2570708 < baseStart_2570708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570721 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 2, 2, 6]
def baseStart_2570721 : Nat := 118140960795 + 2570721 * 2 ^ 59
def prefixEnd_2570721 : Nat := 4983230072969 + 3 ^ 40 * 2570721 * 2
def baseEnd_2570721 : Nat := 1320015501606941775964975

theorem tailTrace_2570721 : CollatzResearch.WordTrace tailWord_2570721 prefixEnd_2570721 1320015501606941775964975 := by
  unfold tailWord_2570721
  simp only [CollatzResearch.WordTrace]
  refine ⟨93761897719724336037816017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62507931813149557358544011 93761897719724336037816017)
  ·
    refine ⟨70321423289793252028362013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93761897719724336037816017 70321423289793252028362013)
    ·
      refine ⟨26370533733672469510635755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70321423289793252028362013 26370533733672469510635755)
      ·
        refine ⟨39555800600508704265953633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26370533733672469510635755 39555800600508704265953633)
        ·
          refine ⟨29666850450381528199465225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39555800600508704265953633 29666850450381528199465225)
          ·
            refine ⟨22250137837786146149598919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29666850450381528199465225 22250137837786146149598919)
            ·
              refine ⟨33375206756679219224398379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22250137837786146149598919 33375206756679219224398379)
              ·
                refine ⟨50062810135018828836597569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33375206756679219224398379 50062810135018828836597569)
                ·
                  refine ⟨37547107601264121627448177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50062810135018828836597569 37547107601264121627448177)
                  ·
                    refine ⟨28160330700948091220586133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37547107601264121627448177 28160330700948091220586133)
                    ·
                      refine ⟨1320015501606941775964975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28160330700948091220586133 1320015501606941775964975)
                      ·
                        rfl

theorem cell23_2570721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_2570721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570721 prefixEnd_2570721 := by exact prefixLift 2570721
  have htrace : WordTrace (prefixWord ++ tailWord_2570721) baseStart_2570721 baseEnd_2570721 := by
    simpa [prefixWord, tailWord_2570721, baseEnd_2570721] using wordTrace_append hprefix tailTrace_2570721
  have hstable : (prefixWord ++ tailWord_2570721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570721).length < 2 ^ (prefixWord ++ tailWord_2570721).sum := by decide
  have hdescent : baseEnd_2570721 < baseStart_2570721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570762 : List Nat := [3, 1, 2, 2, 2, 1, 4, 2, 2, 1, 3]
def baseStart_2570762 : Nat := 118140960795 + 2570762 * 2 ^ 59
def prefixEnd_2570762 : Nat := 4983230072969 + 3 ^ 40 * 2570762 * 2
def baseEnd_2570762 : Nat := 1320036554313776115552287

theorem tailTrace_2570762 : CollatzResearch.WordTrace tailWord_2570762 prefixEnd_2570762 1320036554313776115552287 := by
  unfold tailWord_2570762
  simp only [CollatzResearch.WordTrace]
  refine ⟨23440848278143950010014635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62508928741717200026705693 23440848278143950010014635)
  ·
    refine ⟨35161272417215925015021953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23440848278143950010014635 35161272417215925015021953)
    ·
      refine ⟨26370954312911943761266465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35161272417215925015021953 26370954312911943761266465)
      ·
        refine ⟨19778215734683957820949849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26370954312911943761266465 19778215734683957820949849)
        ·
          refine ⟨14833661801012968365712387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19778215734683957820949849 14833661801012968365712387)
          ·
            refine ⟨22250492701519452548568581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14833661801012968365712387 22250492701519452548568581)
            ·
              refine ⟨4171967381534897352856609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22250492701519452548568581 4171967381534897352856609)
              ·
                refine ⟨3128975536151173014642457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4171967381534897352856609 3128975536151173014642457)
                ·
                  refine ⟨2346731652113379760981843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3128975536151173014642457 2346731652113379760981843)
                  ·
                    refine ⟨3520097478170069641472765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2346731652113379760981843 3520097478170069641472765)
                    ·
                      refine ⟨1320036554313776115552287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3520097478170069641472765 1320036554313776115552287)
                      ·
                        rfl

theorem cell23_2570762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_2570762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570762 prefixEnd_2570762 := by exact prefixLift 2570762
  have htrace : WordTrace (prefixWord ++ tailWord_2570762) baseStart_2570762 baseEnd_2570762 := by
    simpa [prefixWord, tailWord_2570762, baseEnd_2570762] using wordTrace_append hprefix tailTrace_2570762
  have hstable : (prefixWord ++ tailWord_2570762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570762).length < 2 ^ (prefixWord ++ tailWord_2570762).sum := by decide
  have hdescent : baseEnd_2570762 < baseStart_2570762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570806 : List Nat := [5, 1, 2, 1, 2, 1, 4, 1, 1, 3, 2]
def baseStart_2570806 : Nat := 118140960795 + 2570806 * 2 ^ 59
def prefixEnd_2570806 : Nat := 4983230072969 + 3 ^ 40 * 2570806 * 2
def baseEnd_2570806 : Nat := 1320059147462573943402085

theorem tailTrace_2570806 : CollatzResearch.WordTrace tailWord_2570806 prefixEnd_2570806 1320059147462573943402085 := by
  unfold tailWord_2570806
  simp only [CollatzResearch.WordTrace]
  refine ⟨5860312370276024722166267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62509998616277597036440181 5860312370276024722166267)
  ·
    refine ⟨8790468555414037083249401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5860312370276024722166267 8790468555414037083249401)
    ·
      refine ⟨6592851416560527812437051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8790468555414037083249401 6592851416560527812437051)
      ·
        refine ⟨9889277124840791718655577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6592851416560527812437051 9889277124840791718655577)
        ·
          refine ⟨7416957843630593788991683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9889277124840791718655577 7416957843630593788991683)
          ·
            refine ⟨11125436765445890683487525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7416957843630593788991683 11125436765445890683487525)
            ·
              refine ⟨2086019393521104503153911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11125436765445890683487525 2086019393521104503153911)
              ·
                refine ⟨3129029090281656754730867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2086019393521104503153911 3129029090281656754730867)
                ·
                  refine ⟨4693543635422485132096301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3129029090281656754730867 4693543635422485132096301)
                  ·
                    refine ⟨1760078863283431924536113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4693543635422485132096301 1760078863283431924536113)
                    ·
                      refine ⟨1320059147462573943402085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1760078863283431924536113 1320059147462573943402085)
                      ·
                        rfl

theorem cell23_2570806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_2570806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570806 prefixEnd_2570806 := by exact prefixLift 2570806
  have htrace : WordTrace (prefixWord ++ tailWord_2570806) baseStart_2570806 baseEnd_2570806 := by
    simpa [prefixWord, tailWord_2570806, baseEnd_2570806] using wordTrace_append hprefix tailTrace_2570806
  have hstable : (prefixWord ++ tailWord_2570806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570806).length < 2 ^ (prefixWord ++ tailWord_2570806).sum := by decide
  have hdescent : baseEnd_2570806 < baseStart_2570806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570811 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 8]
def baseStart_2570811 : Nat := 118140960795 + 2570811 * 2 ^ 59
def prefixEnd_2570811 : Nat := 4983230072969 + 3 ^ 40 * 2570811 * 2
def baseEnd_2570811 : Nat := 1320061714865846423839561

theorem tailTrace_2570811 : CollatzResearch.WordTrace tailWord_2570811 prefixEnd_2570811 1320061714865846423839561 := by
  unfold tailWord_2570811
  simp only [CollatzResearch.WordTrace]
  refine ⟨93765180289398281408592287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62510120192932187605728191 93765180289398281408592287)
  ·
    refine ⟨140647770434097422112888431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93765180289398281408592287 140647770434097422112888431)
    ·
      refine ⟨210971655651146133169332647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140647770434097422112888431 210971655651146133169332647)
      ·
        refine ⟨316457483476719199753998971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210971655651146133169332647 316457483476719199753998971)
        ·
          refine ⟨474686225215078799630998457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316457483476719199753998971 474686225215078799630998457)
          ·
            refine ⟨356014668911309099723248843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 474686225215078799630998457 356014668911309099723248843)
            ·
              refine ⟨534022003366963649584873265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356014668911309099723248843 534022003366963649584873265)
              ·
                refine ⟨400516502525222737188654949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 534022003366963649584873265 400516502525222737188654949)
                ·
                  refine ⟨75096844223479263222872803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 400516502525222737188654949 75096844223479263222872803)
                  ·
                    refine ⟨112645266335218894834309205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75096844223479263222872803 112645266335218894834309205)
                    ·
                      refine ⟨1320061714865846423839561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 112645266335218894834309205 1320061714865846423839561)
                      ·
                        rfl

theorem cell23_2570811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 8].length) (baseStart_2570811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570811 prefixEnd_2570811 := by exact prefixLift 2570811
  have htrace : WordTrace (prefixWord ++ tailWord_2570811) baseStart_2570811 baseEnd_2570811 := by
    simpa [prefixWord, tailWord_2570811, baseEnd_2570811] using wordTrace_append hprefix tailTrace_2570811
  have hstable : (prefixWord ++ tailWord_2570811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570811).length < 2 ^ (prefixWord ++ tailWord_2570811).sum := by decide
  have hdescent : baseEnd_2570811 < baseStart_2570811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570836 : List Nat := [2, 4, 1, 1, 1, 4, 3, 1, 2, 2, 2]
def baseStart_2570836 : Nat := 118140960795 + 2570836 * 2 ^ 59
def prefixEnd_2570836 : Nat := 4983230072969 + 3 ^ 40 * 2570836 * 2
def baseEnd_2570836 : Nat := 1320074551882208826026947

theorem tailTrace_2570836 : CollatzResearch.WordTrace tailWord_2570836 prefixEnd_2570836 1320074551882208826026947 := by
  unfold tailWord_2570836
  simp only [CollatzResearch.WordTrace]
  refine ⟨46883046057153855339126181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62510728076205140452168241 46883046057153855339126181)
  ·
    refine ⟨8790571135716347876086159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46883046057153855339126181 8790571135716347876086159)
    ·
      refine ⟨13185856703574521814129239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8790571135716347876086159 13185856703574521814129239)
      ·
        refine ⟨19778785055361782721193859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13185856703574521814129239 19778785055361782721193859)
        ·
          refine ⟨29668177583042674081790789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19778785055361782721193859 29668177583042674081790789)
          ·
            refine ⟨5562783296820501390335773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29668177583042674081790789 5562783296820501390335773)
            ·
              refine ⟨2086043736307688021375915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5562783296820501390335773 2086043736307688021375915)
              ·
                refine ⟨3129065604461532032063873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2086043736307688021375915 3129065604461532032063873)
                ·
                  refine ⟨2346799203346149024047905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3129065604461532032063873 2346799203346149024047905)
                  ·
                    refine ⟨1760099402509611768035929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2346799203346149024047905 1760099402509611768035929)
                    ·
                      refine ⟨1320074551882208826026947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1760099402509611768035929 1320074551882208826026947)
                      ·
                        rfl

theorem cell23_2570836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_2570836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570836 prefixEnd_2570836 := by exact prefixLift 2570836
  have htrace : WordTrace (prefixWord ++ tailWord_2570836) baseStart_2570836 baseEnd_2570836 := by
    simpa [prefixWord, tailWord_2570836, baseEnd_2570836] using wordTrace_append hprefix tailTrace_2570836
  have hstable : (prefixWord ++ tailWord_2570836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570836).length < 2 ^ (prefixWord ++ tailWord_2570836).sum := by decide
  have hdescent : baseEnd_2570836 < baseStart_2570836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570875 : List Nat := [1, 1, 1, 1, 1, 4, 2, 4, 2, 4, 2]
def baseStart_2570875 : Nat := 118140960795 + 2570875 * 2 ^ 59
def prefixEnd_2570875 : Nat := 4983230072969 + 3 ^ 40 * 2570875 * 2
def baseEnd_2570875 : Nat := 1320094577627734173439267

theorem tailTrace_2570875 : CollatzResearch.WordTrace tailWord_2570875 prefixEnd_2570875 1320094577627734173439267 := by
  unfold tailWord_2570875
  simp only [CollatzResearch.WordTrace]
  refine ⟨93767514561166420338922079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62511676374110946892614719 93767514561166420338922079)
  ·
    refine ⟨140651271841749630508383119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93767514561166420338922079 140651271841749630508383119)
    ·
      refine ⟨210976907762624445762574679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140651271841749630508383119 210976907762624445762574679)
      ·
        refine ⟨316465361643936668643862019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210976907762624445762574679 316465361643936668643862019)
        ·
          refine ⟨474698042465905002965793029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316465361643936668643862019 474698042465905002965793029)
          ·
            refine ⟨89005882962357188056086193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 474698042465905002965793029 89005882962357188056086193)
            ·
              refine ⟨66754412221767891042064645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89005882962357188056086193 66754412221767891042064645)
              ·
                refine ⟨12516452291581479570387121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66754412221767891042064645 12516452291581479570387121)
                ·
                  refine ⟨9387339218686109677790341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12516452291581479570387121 9387339218686109677790341)
                  ·
                    refine ⟨1760126103503645564585689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9387339218686109677790341 1760126103503645564585689)
                    ·
                      refine ⟨1320094577627734173439267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1760126103503645564585689 1320094577627734173439267)
                      ·
                        rfl

theorem cell23_2570875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 4, 2].length) (baseStart_2570875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570875 prefixEnd_2570875 := by exact prefixLift 2570875
  have htrace : WordTrace (prefixWord ++ tailWord_2570875) baseStart_2570875 baseEnd_2570875 := by
    simpa [prefixWord, tailWord_2570875, baseEnd_2570875] using wordTrace_append hprefix tailTrace_2570875
  have hstable : (prefixWord ++ tailWord_2570875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570875).length < 2 ^ (prefixWord ++ tailWord_2570875).sum := by decide
  have hdescent : baseEnd_2570875 < baseStart_2570875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570975 : List Nat := [1, 1, 2, 3, 2, 3, 2, 2, 1, 6]
def baseStart_2570975 : Nat := 118140960795 + 2570975 * 2 ^ 59
def prefixEnd_2570975 : Nat := 4983230072969 + 3 ^ 40 * 2570975 * 2
def baseEnd_2570975 : Nat := 440048641897727927396269

theorem tailTrace_2570975 : CollatzResearch.WordTrace tailWord_2570975 prefixEnd_2570975 440048641897727927396269 := by
  unfold tailWord_2570975
  simp only [CollatzResearch.WordTrace]
  refine ⟨93771161860804137417562379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62514107907202758278374919 93771161860804137417562379)
  ·
    refine ⟨140656742791206206126343569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93771161860804137417562379 140656742791206206126343569)
    ·
      refine ⟨105492557093404654594757677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140656742791206206126343569 105492557093404654594757677)
      ·
        refine ⟨39559708910026745473034129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105492557093404654594757677 39559708910026745473034129)
        ·
          refine ⟨29669781682520059104775597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39559708910026745473034129 29669781682520059104775597)
          ·
            refine ⟨11126168130945022164290849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29669781682520059104775597 11126168130945022164290849)
            ·
              refine ⟨8344626098208766623218137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11126168130945022164290849 8344626098208766623218137)
              ·
                refine ⟨6258469573656574967413603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8344626098208766623218137 6258469573656574967413603)
                ·
                  refine ⟨9387704360484862451120405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6258469573656574967413603 9387704360484862451120405)
                  ·
                    refine ⟨440048641897727927396269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9387704360484862451120405 440048641897727927396269)
                    ·
                      rfl

theorem cell23_2570975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 6].length) (baseStart_2570975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570975 prefixEnd_2570975 := by exact prefixLift 2570975
  have htrace : WordTrace (prefixWord ++ tailWord_2570975) baseStart_2570975 baseEnd_2570975 := by
    simpa [prefixWord, tailWord_2570975, baseEnd_2570975] using wordTrace_append hprefix tailTrace_2570975
  have hstable : (prefixWord ++ tailWord_2570975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570975).length < 2 ^ (prefixWord ++ tailWord_2570975).sum := by decide
  have hdescent : baseEnd_2570975 < baseStart_2570975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2570979 : List Nat := [1, 1, 1, 7, 1, 1, 4, 1, 1, 5]
def baseStart_2570979 : Nat := 118140960795 + 2570979 * 2 ^ 59
def prefixEnd_2570979 : Nat := 4983230072969 + 3 ^ 40 * 2570979 * 2
def baseEnd_2570979 : Nat := 440049326538600588846263

theorem tailTrace_2570979 : CollatzResearch.WordTrace tailWord_2570979 prefixEnd_2570979 440049326538600588846263 := by
  unfold tailWord_2570979
  simp only [CollatzResearch.WordTrace]
  refine ⟨93771307752789646100707991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62514205168526430733805327 93771307752789646100707991)
  ·
    refine ⟨140656961629184469151061987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93771307752789646100707991 140656961629184469151061987)
    ·
      refine ⟨210985442443776703726592981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140656961629184469151061987 210985442443776703726592981)
      ·
        refine ⟨4944971307276016493592023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 210985442443776703726592981 4944971307276016493592023)
        ·
          refine ⟨7417456960914024740388035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4944971307276016493592023 7417456960914024740388035)
          ·
            refine ⟨11126185441371037110582053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7417456960914024740388035 11126185441371037110582053)
            ·
              refine ⟨2086159770257069458234135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11126185441371037110582053 2086159770257069458234135)
              ·
                refine ⟨3129239655385604187351203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2086159770257069458234135 3129239655385604187351203)
                ·
                  refine ⟨4693859483078406281026805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3129239655385604187351203 4693859483078406281026805)
                  ·
                    refine ⟨440049326538600588846263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4693859483078406281026805 440049326538600588846263)
                    ·
                      rfl

theorem cell23_2570979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 1, 5].length) (baseStart_2570979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2570979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2570979 prefixEnd_2570979 := by exact prefixLift 2570979
  have htrace : WordTrace (prefixWord ++ tailWord_2570979) baseStart_2570979 baseEnd_2570979 := by
    simpa [prefixWord, tailWord_2570979, baseEnd_2570979] using wordTrace_append hprefix tailTrace_2570979
  have hstable : (prefixWord ++ tailWord_2570979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2570979).length < 2 ^ (prefixWord ++ tailWord_2570979).sum := by decide
  have hdescent : baseEnd_2570979 < baseStart_2570979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2570979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571045 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 2, 2, 5]
def baseStart_2571045 : Nat := 118140960795 + 2571045 * 2 ^ 59
def prefixEnd_2571045 : Nat := 4983230072969 + 3 ^ 40 * 2571045 * 2
def baseEnd_2571045 : Nat := 1320181869338998508313485

theorem tailTrace_2571045 : CollatzResearch.WordTrace tailWord_2571045 prefixEnd_2571045 1320181869338998508313485 := by
  unfold tailWord_2571045
  simp only [CollatzResearch.WordTrace]
  refine ⟨93773714970550539372610589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62515809980367026248407059 93773714970550539372610589)
  ·
    refine ⟨35165143113956452264728971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93773714970550539372610589 35165143113956452264728971)
    ·
      refine ⟨52747714670934678397093457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35165143113956452264728971 52747714670934678397093457)
      ·
        refine ⟨39560786003201008797820093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52747714670934678397093457 39560786003201008797820093)
        ·
          refine ⟨14835294751200378299182535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39560786003201008797820093 14835294751200378299182535)
          ·
            refine ⟨22252942126800567448773803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14835294751200378299182535 22252942126800567448773803)
            ·
              refine ⟨33379413190200851173160705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22252942126800567448773803 33379413190200851173160705)
              ·
                refine ⟨25034559892650638379870529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33379413190200851173160705 25034559892650638379870529)
                ·
                  refine ⟨18775919919487978784902897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25034559892650638379870529 18775919919487978784902897)
                  ·
                    refine ⟨14081939939615984088677173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18775919919487978784902897 14081939939615984088677173)
                    ·
                      refine ⟨1320181869338998508313485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14081939939615984088677173 1320181869338998508313485)
                      ·
                        rfl

theorem cell23_2571045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_2571045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571045 prefixEnd_2571045 := by exact prefixLift 2571045
  have htrace : WordTrace (prefixWord ++ tailWord_2571045) baseStart_2571045 baseEnd_2571045 := by
    simpa [prefixWord, tailWord_2571045, baseEnd_2571045] using wordTrace_append hprefix tailTrace_2571045
  have hstable : (prefixWord ++ tailWord_2571045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571045).length < 2 ^ (prefixWord ++ tailWord_2571045).sum := by decide
  have hdescent : baseEnd_2571045 < baseStart_2571045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571050 : List Nat := [3, 1, 4, 3, 1, 2, 1, 1, 3, 2, 2]
def baseStart_2571050 : Nat := 118140960795 + 2571050 * 2 ^ 59
def prefixEnd_2571050 : Nat := 4983230072969 + 3 ^ 40 * 2571050 * 2
def baseEnd_2571050 : Nat := 1320184436742270988750963

theorem tailTrace_2571050 : CollatzResearch.WordTrace tailWord_2571050 prefixEnd_2571050 1320184436742270988750963 := by
  unfold tailWord_2571050
  simp only [CollatzResearch.WordTrace]
  refine ⟨23443474333883106306635651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62515931557021616817695069 23443474333883106306635651)
  ·
    refine ⟨35165211500824659459953477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23443474333883106306635651 35165211500824659459953477)
    ·
      refine ⟨6593477156404623648741277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35165211500824659459953477 6593477156404623648741277)
      ·
        refine ⟨2472553933651733868277979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6593477156404623648741277 2472553933651733868277979)
        ·
          refine ⟨3708830900477600802416969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2472553933651733868277979 3708830900477600802416969)
          ·
            refine ⟨2781623175358200601812727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3708830900477600802416969 2781623175358200601812727)
            ·
              refine ⟨4172434763037300902719091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2781623175358200601812727 4172434763037300902719091)
              ·
                refine ⟨6258652144555951354078637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4172434763037300902719091 6258652144555951354078637)
                ·
                  refine ⟨2346994554208481757779489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6258652144555951354078637 2346994554208481757779489)
                  ·
                    refine ⟨1760245915656361318334617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2346994554208481757779489 1760245915656361318334617)
                    ·
                      refine ⟨1320184436742270988750963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1760245915656361318334617 1320184436742270988750963)
                      ·
                        rfl

theorem cell23_2571050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_2571050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571050 prefixEnd_2571050 := by exact prefixLift 2571050
  have htrace : WordTrace (prefixWord ++ tailWord_2571050) baseStart_2571050 baseEnd_2571050 := by
    simpa [prefixWord, tailWord_2571050, baseEnd_2571050] using wordTrace_append hprefix tailTrace_2571050
  have hstable : (prefixWord ++ tailWord_2571050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571050).length < 2 ^ (prefixWord ++ tailWord_2571050).sum := by decide
  have hdescent : baseEnd_2571050 < baseStart_2571050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571060 : List Nat := [2, 5, 1, 1, 4, 1, 2, 1, 2, 4]
def baseStart_2571060 : Nat := 118140960795 + 2571060 * 2 ^ 59
def prefixEnd_2571060 : Nat := 4983230072969 + 3 ^ 40 * 2571060 * 2
def baseEnd_2571060 : Nat := 440063190516271983208639

theorem tailTrace_2571060 : CollatzResearch.WordTrace tailWord_2571060 prefixEnd_2571060 440063190516271983208639 := by
  unfold tailWord_2571060
  simp only [CollatzResearch.WordTrace]
  refine ⟨46887131032748098467203317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62516174710330797956271089 46887131032748098467203317)
  ·
    refine ⟨4395668534320134231300311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46887131032748098467203317 4395668534320134231300311)
    ·
      refine ⟨6593502801480201346950467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4395668534320134231300311 6593502801480201346950467)
      ·
        refine ⟨9890254202220302020425701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6593502801480201346950467 9890254202220302020425701)
        ·
          refine ⟨1854422662916306628829819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9890254202220302020425701 1854422662916306628829819)
          ·
            refine ⟨2781633994374459943244729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1854422662916306628829819 2781633994374459943244729)
            ·
              refine ⟨2086225495780844957433547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2781633994374459943244729 2086225495780844957433547)
              ·
                refine ⟨3129338243671267436150321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2086225495780844957433547 3129338243671267436150321)
                ·
                  refine ⟨2347003682753450577112741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3129338243671267436150321 2347003682753450577112741)
                  ·
                    refine ⟨440063190516271983208639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2347003682753450577112741 440063190516271983208639)
                    ·
                      rfl

theorem cell23_2571060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_2571060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571060 prefixEnd_2571060 := by exact prefixLift 2571060
  have htrace : WordTrace (prefixWord ++ tailWord_2571060) baseStart_2571060 baseEnd_2571060 := by
    simpa [prefixWord, tailWord_2571060, baseEnd_2571060] using wordTrace_append hprefix tailTrace_2571060
  have hstable : (prefixWord ++ tailWord_2571060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571060).length < 2 ^ (prefixWord ++ tailWord_2571060).sum := by decide
  have hdescent : baseEnd_2571060 < baseStart_2571060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571066 : List Nat := [3, 1, 1, 1, 6, 1, 1, 3, 2, 1, 3]
def baseStart_2571066 : Nat := 118140960795 + 2571066 * 2 ^ 59
def prefixEnd_2571066 : Nat := 4983230072969 + 3 ^ 40 * 2571066 * 2
def baseEnd_2571066 : Nat := 1320192652432742926150889

theorem tailTrace_2571066 : CollatzResearch.WordTrace tailWord_2571066 prefixEnd_2571066 1320192652432742926150889 := by
  unfold tailWord_2571066
  simp only [CollatzResearch.WordTrace]
  refine ⟨23443620225868614989781263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62516320602316306639416701 23443620225868614989781263)
  ·
    refine ⟨35165430338802922484671895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23443620225868614989781263 35165430338802922484671895)
    ·
      refine ⟨52748145508204383727007843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35165430338802922484671895 52748145508204383727007843)
      ·
        refine ⟨79122218262306575590511765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52748145508204383727007843 79122218262306575590511765)
        ·
          refine ⟨3708853981045620730805239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 79122218262306575590511765 3708853981045620730805239)
          ·
            refine ⟨5563280971568431096207859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3708853981045620730805239 5563280971568431096207859)
            ·
              refine ⟨8344921457352646644311789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5563280971568431096207859 8344921457352646644311789)
              ·
                refine ⟨3129345546507242491616921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8344921457352646644311789 3129345546507242491616921)
                ·
                  refine ⟨2347009159880431868712691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3129345546507242491616921 2347009159880431868712691)
                  ·
                    refine ⟨3520513739820647803069037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2347009159880431868712691 3520513739820647803069037)
                    ·
                      refine ⟨1320192652432742926150889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3520513739820647803069037 1320192652432742926150889)
                      ·
                        rfl

theorem cell23_2571066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 2, 1, 3].length) (baseStart_2571066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571066 prefixEnd_2571066 := by exact prefixLift 2571066
  have htrace : WordTrace (prefixWord ++ tailWord_2571066) baseStart_2571066 baseEnd_2571066 := by
    simpa [prefixWord, tailWord_2571066, baseEnd_2571066] using wordTrace_append hprefix tailTrace_2571066
  have hstable : (prefixWord ++ tailWord_2571066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571066).length < 2 ^ (prefixWord ++ tailWord_2571066).sum := by decide
  have hdescent : baseEnd_2571066 < baseStart_2571066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571072 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 5, 4, 2]
def baseStart_2571072 : Nat := 118140960795 + 2571072 * 2 ^ 59
def prefixEnd_2571072 : Nat := 4983230072969 + 3 ^ 40 * 2571072 * 2
def baseEnd_2571072 : Nat := 1320195733316669902675861

theorem tailTrace_2571072 : CollatzResearch.WordTrace tailWord_2571072 prefixEnd_2571072 1320195733316669902675861 := by
  unfold tailWord_2571072
  simp only [CollatzResearch.WordTrace]
  refine ⟨46887349870726361491921735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62516466494301815322562313 46887349870726361491921735)
  ·
    refine ⟨70331024806089542237882603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46887349870726361491921735 70331024806089542237882603)
    ·
      refine ⟨105496537209134313356823905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70331024806089542237882603 105496537209134313356823905)
      ·
        refine ⟨79122402906850735017617929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105496537209134313356823905 79122402906850735017617929)
        ·
          refine ⟨59341802180138051263213447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79122402906850735017617929 59341802180138051263213447)
          ·
            refine ⟨89012703270207076894820171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59341802180138051263213447 89012703270207076894820171)
            ·
              refine ⟨133519054905310615342230257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89012703270207076894820171 133519054905310615342230257)
              ·
                refine ⟨100139291178982961506672693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133519054905310615342230257 100139291178982961506672693)
                ·
                  refine ⟨9388058548029652641250565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100139291178982961506672693 9388058548029652641250565)
                  ·
                    refine ⟨1760260977755559870234481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9388058548029652641250565 1760260977755559870234481)
                    ·
                      refine ⟨1320195733316669902675861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1760260977755559870234481 1320195733316669902675861)
                      ·
                        rfl

theorem cell23_2571072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 5, 4, 2].length) (baseStart_2571072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571072 prefixEnd_2571072 := by exact prefixLift 2571072
  have htrace : WordTrace (prefixWord ++ tailWord_2571072) baseStart_2571072 baseEnd_2571072 := by
    simpa [prefixWord, tailWord_2571072, baseEnd_2571072] using wordTrace_append hprefix tailTrace_2571072
  have hstable : (prefixWord ++ tailWord_2571072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571072).length < 2 ^ (prefixWord ++ tailWord_2571072).sum := by decide
  have hdescent : baseEnd_2571072 < baseStart_2571072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571075 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 5]
def baseStart_2571075 : Nat := 118140960795 + 2571075 * 2 ^ 59
def prefixEnd_2571075 : Nat := 4983230072969 + 3 ^ 40 * 2571075 * 2
def baseEnd_2571075 : Nat := 1320197273758633390938347

theorem tailTrace_2571075 : CollatzResearch.WordTrace tailWord_2571075 prefixEnd_2571075 1320197273758633390938347 := by
  unfold tailWord_2571075
  simp only [CollatzResearch.WordTrace]
  refine ⟨93774809160441854496202679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62516539440294569664135119 93774809160441854496202679)
  ·
    refine ⟨140662213740662781744304019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93774809160441854496202679 140662213740662781744304019)
    ·
      refine ⟨210993320610994172616456029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140662213740662781744304019 210993320610994172616456029)
      ·
        refine ⟨79122495229122814731171011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210993320610994172616456029 79122495229122814731171011)
        ·
          refine ⟨118683742843684222096756517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79122495229122814731171011 118683742843684222096756517)
          ·
            refine ⟨22253201783190791643141847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118683742843684222096756517 22253201783190791643141847)
            ·
              refine ⟨33379802674786187464712771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22253201783190791643141847 33379802674786187464712771)
              ·
                refine ⟨50069704012179281197069157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33379802674786187464712771 50069704012179281197069157)
                ·
                  refine ⟨9388069502283615224450467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50069704012179281197069157 9388069502283615224450467)
                  ·
                    refine ⟨14082104253425422836675701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9388069502283615224450467 14082104253425422836675701)
                    ·
                      refine ⟨1320197273758633390938347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14082104253425422836675701 1320197273758633390938347)
                      ·
                        rfl

theorem cell23_2571075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_2571075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571075 prefixEnd_2571075 := by exact prefixLift 2571075
  have htrace : WordTrace (prefixWord ++ tailWord_2571075) baseStart_2571075 baseEnd_2571075 := by
    simpa [prefixWord, tailWord_2571075, baseEnd_2571075] using wordTrace_append hprefix tailTrace_2571075
  have hstable : (prefixWord ++ tailWord_2571075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571075).length < 2 ^ (prefixWord ++ tailWord_2571075).sum := by decide
  have hdescent : baseEnd_2571075 < baseStart_2571075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571122 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 1, 5, 3]
def baseStart_2571122 : Nat := 118140960795 + 2571122 * 2 ^ 59
def prefixEnd_2571122 : Nat := 4983230072969 + 3 ^ 40 * 2571122 * 2
def baseEnd_2571122 : Nat := 1320221407349394707050631

theorem tailTrace_2571122 : CollatzResearch.WordTrace tailWord_2571122 prefixEnd_2571122 1320221407349394707050631 := by
  unfold tailWord_2571122
  simp only [CollatzResearch.WordTrace]
  refine ⟨23444130847817895380790905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62517682260847721015442413 23444130847817895380790905)
  ·
    refine ⟨17583098135863421535593179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23444130847817895380790905 17583098135863421535593179)
    ·
      refine ⟨26374647203795132303389769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17583098135863421535593179 26374647203795132303389769)
      ·
        refine ⟨19780985402846349227542327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26374647203795132303389769 19780985402846349227542327)
        ·
          refine ⟨29671478104269523841313491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19780985402846349227542327 29671478104269523841313491)
          ·
            refine ⟨44507217156404285761970237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29671478104269523841313491 44507217156404285761970237)
            ·
              refine ⟨16690206433651607160738839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44507217156404285761970237 16690206433651607160738839)
              ·
                refine ⟨25035309650477410741108259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16690206433651607160738839 25035309650477410741108259)
                ·
                  refine ⟨37552964475716116111662389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25035309650477410741108259 37552964475716116111662389)
                  ·
                    refine ⟨3520590419598385885468349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37552964475716116111662389 3520590419598385885468349)
                    ·
                      refine ⟨1320221407349394707050631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3520590419598385885468349 1320221407349394707050631)
                      ·
                        rfl

theorem cell23_2571122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_2571122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571122 prefixEnd_2571122 := by exact prefixLift 2571122
  have htrace : WordTrace (prefixWord ++ tailWord_2571122) baseStart_2571122 baseEnd_2571122 := by
    simpa [prefixWord, tailWord_2571122, baseEnd_2571122] using wordTrace_append hprefix tailTrace_2571122
  have hstable : (prefixWord ++ tailWord_2571122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571122).length < 2 ^ (prefixWord ++ tailWord_2571122).sum := by decide
  have hdescent : baseEnd_2571122 < baseStart_2571122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571135 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 7]
def baseStart_2571135 : Nat := 118140960795 + 2571135 * 2 ^ 59
def prefixEnd_2571135 : Nat := 4983230072969 + 3 ^ 40 * 2571135 * 2
def baseEnd_2571135 : Nat := 1320228082597903156188071

theorem tailTrace_2571135 : CollatzResearch.WordTrace tailWord_2571135 prefixEnd_2571135 1320228082597903156188071 := by
  unfold tailWord_2571135
  simp only [CollatzResearch.WordTrace]
  refine ⟨93776997540224484743386859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62517998360149656495591239 93776997540224484743386859)
  ·
    refine ⟨140665496310336727115080289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93776997540224484743386859 140665496310336727115080289)
    ·
      refine ⟨105499122232752545336310217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140665496310336727115080289 105499122232752545336310217)
      ·
        refine ⟨79124341674564409002232663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105499122232752545336310217 79124341674564409002232663)
        ·
          refine ⟨118686512511846613503348995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79124341674564409002232663 118686512511846613503348995)
          ·
            refine ⟨178029768767769920255023493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118686512511846613503348995 178029768767769920255023493)
            ·
              refine ⟨33380581643956860047816905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 178029768767769920255023493 33380581643956860047816905)
              ·
                refine ⟨25035436232967645035862679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33380581643956860047816905 25035436232967645035862679)
                ·
                  refine ⟨37553154349451467553794019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25035436232967645035862679 37553154349451467553794019)
                  ·
                    refine ⟨56329731524177201330691029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37553154349451467553794019 56329731524177201330691029)
                    ·
                      refine ⟨1320228082597903156188071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 56329731524177201330691029 1320228082597903156188071)
                      ·
                        rfl

theorem cell23_2571135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_2571135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571135 prefixEnd_2571135 := by exact prefixLift 2571135
  have htrace : WordTrace (prefixWord ++ tailWord_2571135) baseStart_2571135 baseEnd_2571135 := by
    simpa [prefixWord, tailWord_2571135, baseEnd_2571135] using wordTrace_append hprefix tailTrace_2571135
  have hstable : (prefixWord ++ tailWord_2571135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571135).length < 2 ^ (prefixWord ++ tailWord_2571135).sum := by decide
  have hdescent : baseEnd_2571135 < baseStart_2571135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571146 : List Nat := [3, 1, 2, 4, 1, 2, 2, 3, 5]
def baseStart_2571146 : Nat := 118140960795 + 2571146 * 2 ^ 59
def prefixEnd_2571146 : Nat := 4983230072969 + 3 ^ 40 * 2571146 * 2
def baseEnd_2571146 : Nat := 146692636765011401461169

theorem tailTrace_2571146 : CollatzResearch.WordTrace tailWord_2571146 prefixEnd_2571146 146692636765011401461169 := by
  unfold tailWord_2571146
  simp only [CollatzResearch.WordTrace]
  refine ⟨23444349685796158405509323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62518265828789755748024861 23444349685796158405509323)
  ·
    refine ⟨35166524528694237608263985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23444349685796158405509323 35166524528694237608263985)
    ·
      refine ⟨26374893396520678206197989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35166524528694237608263985 26374893396520678206197989)
      ·
        refine ⟨4945292511847627163662123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26374893396520678206197989 4945292511847627163662123)
        ·
          refine ⟨7417938767771440745493185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4945292511847627163662123 7417938767771440745493185)
          ·
            refine ⟨5563454075828580559119889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7417938767771440745493185 5563454075828580559119889)
            ·
              refine ⟨4172590556871435419339917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5563454075828580559119889 4172590556871435419339917)
              ·
                refine ⟨1564721458826788282252469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4172590556871435419339917 1564721458826788282252469)
                ·
                  refine ⟨146692636765011401461169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1564721458826788282252469 146692636765011401461169)
                  ·
                    rfl

theorem cell23_2571146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 3, 5].length) (baseStart_2571146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571146 prefixEnd_2571146 := by exact prefixLift 2571146
  have htrace : WordTrace (prefixWord ++ tailWord_2571146) baseStart_2571146 baseEnd_2571146 := by
    simpa [prefixWord, tailWord_2571146, baseEnd_2571146] using wordTrace_append hprefix tailTrace_2571146
  have hstable : (prefixWord ++ tailWord_2571146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571146).length < 2 ^ (prefixWord ++ tailWord_2571146).sum := by decide
  have hdescent : baseEnd_2571146 < baseStart_2571146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571189 : List Nat := [1, 3, 3, 2, 1, 1, 1, 4, 3, 4]
def baseStart_2571189 : Nat := 118140960795 + 2571189 * 2 ^ 59
def prefixEnd_2571189 : Nat := 4983230072969 + 3 ^ 40 * 2571189 * 2
def baseEnd_2571189 : Nat := 440085270184415314970941

theorem tailTrace_2571189 : CollatzResearch.WordTrace tailWord_2571189 prefixEnd_2571189 440085270184415314970941 := by
  unfold tailWord_2571189
  simp only [CollatzResearch.WordTrace]
  refine ⟨93778967082028851965852621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62519311388019234643901747 93778967082028851965852621)
  ·
    refine ⟨35167112655760819487194733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93778967082028851965852621 35167112655760819487194733)
    ·
      refine ⟨13187667245910307307698025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35167112655760819487194733 13187667245910307307698025)
      ·
        refine ⟨9890750434432730480773519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13187667245910307307698025 9890750434432730480773519)
        ·
          refine ⟨14836125651649095721160279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9890750434432730480773519 14836125651649095721160279)
          ·
            refine ⟨22254188477473643581740419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14836125651649095721160279 22254188477473643581740419)
            ·
              refine ⟨33381282716210465372610629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22254188477473643581740419 33381282716210465372610629)
              ·
                refine ⟨6258990509289462257364493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33381282716210465372610629 6258990509289462257364493)
                ·
                  refine ⟨2347121440983548346511685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6258990509289462257364493 2347121440983548346511685)
                  ·
                    refine ⟨440085270184415314970941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2347121440983548346511685 440085270184415314970941)
                    ·
                      rfl

theorem cell23_2571189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_2571189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571189 prefixEnd_2571189 := by exact prefixLift 2571189
  have htrace : WordTrace (prefixWord ++ tailWord_2571189) baseStart_2571189 baseEnd_2571189 := by
    simpa [prefixWord, tailWord_2571189, baseEnd_2571189] using wordTrace_append hprefix tailTrace_2571189
  have hstable : (prefixWord ++ tailWord_2571189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571189).length < 2 ^ (prefixWord ++ tailWord_2571189).sum := by decide
  have hdescent : baseEnd_2571189 < baseStart_2571189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571249 : List Nat := [1, 2, 2, 2, 4, 2, 1, 1, 3, 5]
def baseStart_2571249 : Nat := 118140960795 + 2571249 * 2 ^ 59
def prefixEnd_2571249 : Nat := 4983230072969 + 3 ^ 40 * 2571249 * 2
def baseEnd_2571249 : Nat := 440095539797505236720849

theorem tailTrace_2571249 : CollatzResearch.WordTrace tailWord_2571249 prefixEnd_2571249 440095539797505236720849 := by
  unfold tailWord_2571249
  simp only [CollatzResearch.WordTrace]
  refine ⟨93781155461811482213036801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62520770307874321475357867 93781155461811482213036801)
  ·
    refine ⟨70335866596358611659777601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93781155461811482213036801 70335866596358611659777601)
    ·
      refine ⟨52751899947268958744833201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70335866596358611659777601 52751899947268958744833201)
      ·
        refine ⟨39563924960451719058624901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52751899947268958744833201 39563924960451719058624901)
        ·
          refine ⟨7418235930084697323492169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39563924960451719058624901 7418235930084697323492169)
          ·
            refine ⟨5563676947563522992619127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7418235930084697323492169 5563676947563522992619127)
            ·
              refine ⟨8345515421345284488928691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5563676947563522992619127 8345515421345284488928691)
              ·
                refine ⟨12518273132017926733393037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8345515421345284488928691 12518273132017926733393037)
                ·
                  refine ⟨4694352424506722525022389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12518273132017926733393037 4694352424506722525022389)
                  ·
                    refine ⟨440095539797505236720849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4694352424506722525022389 440095539797505236720849)
                    ·
                      rfl

theorem cell23_2571249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 5].length) (baseStart_2571249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571249 prefixEnd_2571249 := by exact prefixLift 2571249
  have htrace : WordTrace (prefixWord ++ tailWord_2571249) baseStart_2571249 baseEnd_2571249 := by
    simpa [prefixWord, tailWord_2571249, baseEnd_2571249] using wordTrace_append hprefix tailTrace_2571249
  have hstable : (prefixWord ++ tailWord_2571249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571249).length < 2 ^ (prefixWord ++ tailWord_2571249).sum := by decide
  have hdescent : baseEnd_2571249 < baseStart_2571249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571289 : List Nat := [1, 2, 1, 2, 1, 1, 5, 2, 3, 2, 3]
def baseStart_2571289 : Nat := 118140960795 + 2571289 * 2 ^ 59
def prefixEnd_2571289 : Nat := 4983230072969 + 3 ^ 40 * 2571289 * 2
def baseEnd_2571289 : Nat := 1320307158618695553662363

theorem tailTrace_2571289 : CollatzResearch.WordTrace tailWord_2571289 prefixEnd_2571289 1320307158618695553662363 := by
  unfold tailWord_2571289
  simp only [CollatzResearch.WordTrace]
  refine ⟨93782614381666569044492921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62521742921111046029661947 93782614381666569044492921)
  ·
    refine ⟨70336960786249926783369691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93782614381666569044492921 70336960786249926783369691)
    ·
      refine ⟨105505441179374890175054537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70336960786249926783369691 105505441179374890175054537)
      ·
        refine ⟨79129080884531167631290903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105505441179374890175054537 79129080884531167631290903)
        ·
          refine ⟨118693621326796751446936355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79129080884531167631290903 118693621326796751446936355)
          ·
            refine ⟨178040431990195127170404533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118693621326796751446936355 178040431990195127170404533)
            ·
              refine ⟨16691290499080793172225425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 178040431990195127170404533 16691290499080793172225425)
              ·
                refine ⟨12518467874310594879169069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16691290499080793172225425 12518467874310594879169069)
                ·
                  refine ⟨4694425452866473079688401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12518467874310594879169069 4694425452866473079688401)
                  ·
                    refine ⟨3520819089649854809766301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4694425452866473079688401 3520819089649854809766301)
                    ·
                      refine ⟨1320307158618695553662363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3520819089649854809766301 1320307158618695553662363)
                      ·
                        rfl

theorem cell23_2571289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 2, 3].length) (baseStart_2571289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571289 prefixEnd_2571289 := by exact prefixLift 2571289
  have htrace : WordTrace (prefixWord ++ tailWord_2571289) baseStart_2571289 baseEnd_2571289 := by
    simpa [prefixWord, tailWord_2571289, baseEnd_2571289] using wordTrace_append hprefix tailTrace_2571289
  have hstable : (prefixWord ++ tailWord_2571289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571289).length < 2 ^ (prefixWord ++ tailWord_2571289).sum := by decide
  have hdescent : baseEnd_2571289 < baseStart_2571289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571299 : List Nat := [1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 4]
def baseStart_2571299 : Nat := 118140960795 + 2571299 * 2 ^ 59
def prefixEnd_2571299 : Nat := 4983230072969 + 3 ^ 40 * 2571299 * 2
def baseEnd_2571299 : Nat := 1320312293425240514537317

theorem tailTrace_2571299 : CollatzResearch.WordTrace tailWord_2571299 prefixEnd_2571299 1320312293425240514537317 := by
  unfold tailWord_2571299
  simp only [CollatzResearch.WordTrace]
  refine ⟨93782979111630340752356951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62521986074420227168237967 93782979111630340752356951)
  ·
    refine ⟨140674468667445511128535427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93782979111630340752356951 140674468667445511128535427)
    ·
      refine ⟨211011703001168266692803141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140674468667445511128535427 211011703001168266692803141)
      ·
        refine ⟨39564694312719050004900589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 211011703001168266692803141 39564694312719050004900589)
        ·
          refine ⟨14836760367269643751837721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39564694312719050004900589 14836760367269643751837721)
          ·
            refine ⟨11127570275452232813878291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14836760367269643751837721 11127570275452232813878291)
            ·
              refine ⟨16691355413178349220817437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11127570275452232813878291 16691355413178349220817437)
              ·
                refine ⟨6259258279941880957806539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16691355413178349220817437 6259258279941880957806539)
                ·
                  refine ⟨9388887419912821436709809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6259258279941880957806539 9388887419912821436709809)
                  ·
                    refine ⟨7041665564934616077532357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9388887419912821436709809 7041665564934616077532357)
                    ·
                      refine ⟨1320312293425240514537317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7041665564934616077532357 1320312293425240514537317)
                      ·
                        rfl

theorem cell23_2571299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_2571299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571299 prefixEnd_2571299 := by exact prefixLift 2571299
  have htrace : WordTrace (prefixWord ++ tailWord_2571299) baseStart_2571299 baseEnd_2571299 := by
    simpa [prefixWord, tailWord_2571299, baseEnd_2571299] using wordTrace_append hprefix tailTrace_2571299
  have hstable : (prefixWord ++ tailWord_2571299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571299).length < 2 ^ (prefixWord ++ tailWord_2571299).sum := by decide
  have hdescent : baseEnd_2571299 < baseStart_2571299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571320 : List Nat := [2, 1, 2, 1, 5, 1, 1, 5, 1, 2, 2]
def baseStart_2571320 : Nat := 118140960795 + 2571320 * 2 ^ 59
def prefixEnd_2571320 : Nat := 4983230072969 + 3 ^ 40 * 2571320 * 2
def baseEnd_2571320 : Nat := 1320323076518984932374721

theorem tailTrace_2571320 : CollatzResearch.WordTrace tailWord_2571320 prefixEnd_2571320 1320323076518984932374721 := by
  unfold tailWord_2571320
  simp only [CollatzResearch.WordTrace]
  refine ⟨46891872522277130669435707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62522496696369507559247609 46891872522277130669435707)
  ·
    refine ⟨70337808783415696004153561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46891872522277130669435707 70337808783415696004153561)
    ·
      refine ⟨52753356587561772003115171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70337808783415696004153561 52753356587561772003115171)
      ·
        refine ⟨79130034881342658004672757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52753356587561772003115171 79130034881342658004672757)
        ·
          refine ⟨7418440770125874187938071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79130034881342658004672757 7418440770125874187938071)
          ·
            refine ⟨11127661155188811281907107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7418440770125874187938071 11127661155188811281907107)
            ·
              refine ⟨16691491732783216922860661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11127661155188811281907107 16691491732783216922860661)
              ·
                refine ⟨1564827349948426586518187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16691491732783216922860661 1564827349948426586518187)
                ·
                  refine ⟨2347241024922639879777281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1564827349948426586518187 2347241024922639879777281)
                  ·
                    refine ⟨1760430768691979909832961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2347241024922639879777281 1760430768691979909832961)
                    ·
                      refine ⟨1320323076518984932374721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1760430768691979909832961 1320323076518984932374721)
                      ·
                        rfl

theorem cell23_2571320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 5, 1, 2, 2].length) (baseStart_2571320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571320 prefixEnd_2571320 := by exact prefixLift 2571320
  have htrace : WordTrace (prefixWord ++ tailWord_2571320) baseStart_2571320 baseEnd_2571320 := by
    simpa [prefixWord, tailWord_2571320, baseEnd_2571320] using wordTrace_append hprefix tailTrace_2571320
  have hstable : (prefixWord ++ tailWord_2571320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571320).length < 2 ^ (prefixWord ++ tailWord_2571320).sum := by decide
  have hdescent : baseEnd_2571320 < baseStart_2571320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571336 : List Nat := [2, 1, 3, 1, 1, 1, 5, 1, 4, 1, 3]
def baseStart_2571336 : Nat := 118140960795 + 2571336 * 2 ^ 59
def prefixEnd_2571336 : Nat := 4983230072969 + 3 ^ 40 * 2571336 * 2
def baseEnd_2571336 : Nat := 1320331292209456869774647

theorem tailTrace_2571336 : CollatzResearch.WordTrace tailWord_2571336 prefixEnd_2571336 1320331292209456869774647 := by
  unfold tailWord_2571336
  simp only [CollatzResearch.WordTrace]
  refine ⟨46892164306248148035726931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62522885741664197380969241 46892164306248148035726931)
  ·
    refine ⟨70338246459372222053590397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46892164306248148035726931 70338246459372222053590397)
    ·
      refine ⟨26376842422264583270096399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70338246459372222053590397 26376842422264583270096399)
      ·
        refine ⟨39565263633396874905144599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26376842422264583270096399 39565263633396874905144599)
        ·
          refine ⟨59347895450095312357716899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39565263633396874905144599 59347895450095312357716899)
          ·
            refine ⟨89021843175142968536575349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59347895450095312357716899 89021843175142968536575349)
            ·
              refine ⟨8345797797669653300303939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89021843175142968536575349 8345797797669653300303939)
              ·
                refine ⟨12518696696504479950455909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8345797797669653300303939 12518696696504479950455909)
                ·
                  refine ⟨2347255630594589990710483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12518696696504479950455909 2347255630594589990710483)
                  ·
                    refine ⟨3520883445891884986065725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2347255630594589990710483 3520883445891884986065725)
                    ·
                      refine ⟨1320331292209456869774647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3520883445891884986065725 1320331292209456869774647)
                      ·
                        rfl

theorem cell23_2571336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 4, 1, 3].length) (baseStart_2571336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571336 prefixEnd_2571336 := by exact prefixLift 2571336
  have htrace : WordTrace (prefixWord ++ tailWord_2571336) baseStart_2571336 baseEnd_2571336 := by
    simpa [prefixWord, tailWord_2571336, baseEnd_2571336] using wordTrace_append hprefix tailTrace_2571336
  have hstable : (prefixWord ++ tailWord_2571336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571336).length < 2 ^ (prefixWord ++ tailWord_2571336).sum := by decide
  have hdescent : baseEnd_2571336 < baseStart_2571336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571376 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 3, 4, 2]
def baseStart_2571376 : Nat := 118140960795 + 2571376 * 2 ^ 59
def prefixEnd_2571376 : Nat := 4983230072969 + 3 ^ 40 * 2571376 * 2
def baseEnd_2571376 : Nat := 1320351831435636713274463

theorem tailTrace_2571376 : CollatzResearch.WordTrace tailWord_2571376 prefixEnd_2571376 1320351831435636713274463 := by
  unfold tailWord_2571376
  simp only [CollatzResearch.WordTrace]
  refine ⟨46892893766175691451454991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62523858354900921935273321 46892893766175691451454991)
  ·
    refine ⟨70339340649263537177182487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46892893766175691451454991 70339340649263537177182487)
    ·
      refine ⟨105509010973895305765773731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70339340649263537177182487 105509010973895305765773731)
      ·
        refine ⟨158263516460842958648660597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105509010973895305765773731 158263516460842958648660597)
        ·
          refine ⟨14837204668204027373311931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 158263516460842958648660597 14837204668204027373311931)
          ·
            refine ⟨22255807002306041059967897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14837204668204027373311931 22255807002306041059967897)
            ·
              refine ⟨16691855251729530794975923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22255807002306041059967897 16691855251729530794975923)
              ·
                refine ⟨25037782877594296192463885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16691855251729530794975923 25037782877594296192463885)
                ·
                  refine ⟨9389168579097861072173957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25037782877594296192463885 9389168579097861072173957)
                  ·
                    refine ⟨1760469108580848951032617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9389168579097861072173957 1760469108580848951032617)
                    ·
                      refine ⟨1320351831435636713274463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1760469108580848951032617 1320351831435636713274463)
                      ·
                        rfl

theorem cell23_2571376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 3, 4, 2].length) (baseStart_2571376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571376 prefixEnd_2571376 := by exact prefixLift 2571376
  have htrace : WordTrace (prefixWord ++ tailWord_2571376) baseStart_2571376 baseEnd_2571376 := by
    simpa [prefixWord, tailWord_2571376, baseEnd_2571376] using wordTrace_append hprefix tailTrace_2571376
  have hstable : (prefixWord ++ tailWord_2571376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571376).length < 2 ^ (prefixWord ++ tailWord_2571376).sum := by decide
  have hdescent : baseEnd_2571376 < baseStart_2571376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571439 : List Nat := [1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 5]
def baseStart_2571439 : Nat := 118140960795 + 2571439 * 2 ^ 59
def prefixEnd_2571439 : Nat := 4983230072969 + 3 ^ 40 * 2571439 * 2
def baseEnd_2571439 : Nat := 1320384180716869966786673

theorem tailTrace_2571439 : CollatzResearch.WordTrace tailWord_2571439 prefixEnd_2571439 1320384180716869966786673 := by
  unfold tailWord_2571439
  simp only [CollatzResearch.WordTrace]
  refine ⟨93788085331123144662453371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62525390220748763108302247 93788085331123144662453371)
  ·
    refine ⟨140682127996684716993680057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93788085331123144662453371 140682127996684716993680057)
    ·
      refine ⟨105511595997513537745260043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140682127996684716993680057 105511595997513537745260043)
      ·
        refine ⟨158267393996270306617890065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105511595997513537745260043 158267393996270306617890065)
        ·
          refine ⟨118700545497202729963417549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158267393996270306617890065 118700545497202729963417549)
          ·
            refine ⟨44512704561451023736281581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118700545497202729963417549 44512704561451023736281581)
            ·
              refine ⟨16692264210544133901105593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44512704561451023736281581 16692264210544133901105593)
              ·
                refine ⟨12519198157908100425829195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16692264210544133901105593 12519198157908100425829195)
                ·
                  refine ⟨18778797236862150638743793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12519198157908100425829195 18778797236862150638743793)
                  ·
                    refine ⟨14084097927646612979057845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18778797236862150638743793 14084097927646612979057845)
                    ·
                      refine ⟨1320384180716869966786673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14084097927646612979057845 1320384180716869966786673)
                      ·
                        rfl

theorem cell23_2571439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 5].length) (baseStart_2571439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571439 prefixEnd_2571439 := by exact prefixLift 2571439
  have htrace : WordTrace (prefixWord ++ tailWord_2571439) baseStart_2571439 baseEnd_2571439 := by
    simpa [prefixWord, tailWord_2571439, baseEnd_2571439] using wordTrace_append hprefix tailTrace_2571439
  have hstable : (prefixWord ++ tailWord_2571439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571439).length < 2 ^ (prefixWord ++ tailWord_2571439).sum := by decide
  have hdescent : baseEnd_2571439 < baseStart_2571439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571480 : List Nat := [2, 1, 2, 2, 6, 1, 1, 1, 2, 5]
def baseStart_2571480 : Nat := 118140960795 + 2571480 * 2 ^ 59
def prefixEnd_2571480 : Nat := 4983230072969 + 3 ^ 40 * 2571480 * 2
def baseEnd_2571480 : Nat := 440135077807901435457995

theorem tailTrace_2571480 : CollatzResearch.WordTrace tailWord_2571480 prefixEnd_2571480 440135077807901435457995 := by
  unfold tailWord_2571480
  simp only [CollatzResearch.WordTrace]
  refine ⟨46894790361987304332347947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62526387149316405776463929 46894790361987304332347947)
  ·
    refine ⟨70342185542980956498521921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46894790361987304332347947 70342185542980956498521921)
    ·
      refine ⟨52756639157235717373891441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70342185542980956498521921 52756639157235717373891441)
      ·
        refine ⟨39567479367926788030418581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52756639157235717373891441 39567479367926788030418581)
        ·
          refine ⟨1854725595371568188925871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39567479367926788030418581 1854725595371568188925871)
          ·
            refine ⟨2782088393057352283388807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1854725595371568188925871 2782088393057352283388807)
            ·
              refine ⟨4173132589586028425083211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2782088393057352283388807 4173132589586028425083211)
              ·
                refine ⟨6259698884379042637624817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4173132589586028425083211 6259698884379042637624817)
                ·
                  refine ⟨4694774163284281978218613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6259698884379042637624817 4694774163284281978218613)
                  ·
                    refine ⟨440135077807901435457995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4694774163284281978218613 440135077807901435457995)
                    ·
                      rfl

theorem cell23_2571480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 2, 5].length) (baseStart_2571480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571480 prefixEnd_2571480 := by exact prefixLift 2571480
  have htrace : WordTrace (prefixWord ++ tailWord_2571480) baseStart_2571480 baseEnd_2571480 := by
    simpa [prefixWord, tailWord_2571480, baseEnd_2571480] using wordTrace_append hprefix tailTrace_2571480
  have hstable : (prefixWord ++ tailWord_2571480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571480).length < 2 ^ (prefixWord ++ tailWord_2571480).sum := by decide
  have hdescent : baseEnd_2571480 < baseStart_2571480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571523 : List Nat := [1, 1, 1, 3, 2, 5, 3, 1, 6]
def baseStart_2571523 : Nat := 118140960795 + 2571523 * 2 ^ 59
def prefixEnd_2571523 : Nat := 4983230072969 + 3 ^ 40 * 2571523 * 2
def baseEnd_2571523 : Nat := 146714145899094182015143

theorem tailTrace_2571523 : CollatzResearch.WordTrace tailWord_2571523 prefixEnd_2571523 146714145899094182015143 := by
  unfold tailWord_2571523
  simp only [CollatzResearch.WordTrace]
  refine ⟨93791149062818827008511223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62527432708545884672340815 93791149062818827008511223)
  ·
    refine ⟨140686723594228240512766835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93791149062818827008511223 140686723594228240512766835)
    ·
      refine ⟨211030085391342360769150253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140686723594228240512766835 211030085391342360769150253)
      ·
        refine ⟨79136282021753385288431345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211030085391342360769150253 79136282021753385288431345)
        ·
          refine ⟨59352211516315038966323509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79136282021753385288431345 59352211516315038966323509)
          ·
            refine ⟨5564269829654534903092829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59352211516315038966323509 5564269829654534903092829)
            ·
              refine ⟨2086601186120450588659811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5564269829654534903092829 2086601186120450588659811)
              ·
                refine ⟨3129901779180675882989717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2086601186120450588659811 3129901779180675882989717)
                ·
                  refine ⟨146714145899094182015143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3129901779180675882989717 146714145899094182015143)
                  ·
                    rfl

theorem cell23_2571523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 6].length) (baseStart_2571523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571523 prefixEnd_2571523 := by exact prefixLift 2571523
  have htrace : WordTrace (prefixWord ++ tailWord_2571523) baseStart_2571523 baseEnd_2571523 := by
    simpa [prefixWord, tailWord_2571523, baseEnd_2571523] using wordTrace_append hprefix tailTrace_2571523
  have hstable : (prefixWord ++ tailWord_2571523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571523).length < 2 ^ (prefixWord ++ tailWord_2571523).sum := by decide
  have hdescent : baseEnd_2571523 < baseStart_2571523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571543 : List Nat := [1, 1, 3, 4, 1, 1, 1, 3, 1, 5, 2]
def baseStart_2571543 : Nat := 118140960795 + 2571543 * 2 ^ 59
def prefixEnd_2571543 : Nat := 4983230072969 + 3 ^ 40 * 2571543 * 2
def baseEnd_2571543 : Nat := 1320437582704937559886195

theorem tailTrace_2571543 : CollatzResearch.WordTrace tailWord_2571543 prefixEnd_2571543 1320437582704937559886195 := by
  unfold tailWord_2571543
  simp only [CollatzResearch.WordTrace]
  refine ⟨93791878522746370424239283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62527919015164246949492855 93791878522746370424239283)
  ·
    refine ⟨140687817784119555636358925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93791878522746370424239283 140687817784119555636358925)
    ·
      refine ⟨52757931669044833363634597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140687817784119555636358925 52757931669044833363634597)
      ·
        refine ⟨9892112187945906255681487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52757931669044833363634597 9892112187945906255681487)
        ·
          refine ⟨14838168281918859383522231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9892112187945906255681487 14838168281918859383522231)
          ·
            refine ⟨22257252422878289075283347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14838168281918859383522231 22257252422878289075283347)
            ·
              refine ⟨33385878634317433612925021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22257252422878289075283347 33385878634317433612925021)
              ·
                refine ⟨12519704487869037604846883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33385878634317433612925021 12519704487869037604846883)
                ·
                  refine ⟨18779556731803556407270325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12519704487869037604846883 18779556731803556407270325)
                  ·
                    refine ⟨1760583443606583413181593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18779556731803556407270325 1760583443606583413181593)
                    ·
                      refine ⟨1320437582704937559886195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1760583443606583413181593 1320437582704937559886195)
                      ·
                        rfl

theorem cell23_2571543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_2571543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571543 prefixEnd_2571543 := by exact prefixLift 2571543
  have htrace : WordTrace (prefixWord ++ tailWord_2571543) baseStart_2571543 baseEnd_2571543 := by
    simpa [prefixWord, tailWord_2571543, baseEnd_2571543] using wordTrace_append hprefix tailTrace_2571543
  have hstable : (prefixWord ++ tailWord_2571543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571543).length < 2 ^ (prefixWord ++ tailWord_2571543).sum := by decide
  have hdescent : baseEnd_2571543 < baseStart_2571543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571560 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 4, 3, 2]
def baseStart_2571560 : Nat := 118140960795 + 2571560 * 2 ^ 59
def prefixEnd_2571560 : Nat := 4983230072969 + 3 ^ 40 * 2571560 * 2
def baseEnd_2571560 : Nat := 1320446311876063993373617

theorem tailTrace_2571560 : CollatzResearch.WordTrace tailWord_2571560 prefixEnd_2571560 1320446311876063993373617 := by
  unfold tailWord_2571560
  simp only [CollatzResearch.WordTrace]
  refine ⟨46896249281842391163804067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62528332375789854885072089 46896249281842391163804067)
  ·
    refine ⟨70344373922763586745706101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46896249281842391163804067 70344373922763586745706101)
    ·
      refine ⟨6594785055259086257409947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70344373922763586745706101 6594785055259086257409947)
      ·
        refine ⟨9892177582888629386114921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6594785055259086257409947 9892177582888629386114921)
        ·
          refine ⟨7419133187166472039586191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9892177582888629386114921 7419133187166472039586191)
          ·
            refine ⟨11128699780749708059379287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7419133187166472039586191 11128699780749708059379287)
            ·
              refine ⟨16693049671124562089068931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11128699780749708059379287 16693049671124562089068931)
              ·
                refine ⟨25039574506686843133603397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16693049671124562089068931 25039574506686843133603397)
                ·
                  refine ⟨4694920220003783087550637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25039574506686843133603397 4694920220003783087550637)
                  ·
                    refine ⟨1760595082501418657831489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4694920220003783087550637 1760595082501418657831489)
                    ·
                      refine ⟨1320446311876063993373617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1760595082501418657831489 1320446311876063993373617)
                      ·
                        rfl

theorem cell23_2571560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_2571560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571560 prefixEnd_2571560 := by exact prefixLift 2571560
  have htrace : WordTrace (prefixWord ++ tailWord_2571560) baseStart_2571560 baseEnd_2571560 := by
    simpa [prefixWord, tailWord_2571560, baseEnd_2571560] using wordTrace_append hprefix tailTrace_2571560
  have hstable : (prefixWord ++ tailWord_2571560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571560).length < 2 ^ (prefixWord ++ tailWord_2571560).sum := by decide
  have hdescent : baseEnd_2571560 < baseStart_2571560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571574 : List Nat := [5, 1, 2, 3, 1, 2, 2, 1, 6]
def baseStart_2571574 : Nat := 118140960795 + 2571574 * 2 ^ 59
def prefixEnd_2571574 : Nat := 4983230072969 + 3 ^ 40 * 2571574 * 2
def baseEnd_2571574 : Nat := 146717055622802993177617

theorem tailTrace_2571574 : CollatzResearch.WordTrace tailWord_2571574 prefixEnd_2571574 146717055622802993177617 := by
  unfold tailWord_2571574
  simp only [CollatzResearch.WordTrace]
  refine ⟨5862063074102128919913611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62528672790422708479078517 5862063074102128919913611)
  ·
    refine ⟨8793094611153193379870417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5862063074102128919913611 8793094611153193379870417)
    ·
      refine ⟨6594820958364895034902813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8793094611153193379870417 6594820958364895034902813)
      ·
        refine ⟨2473057859386835638088555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6594820958364895034902813 2473057859386835638088555)
        ·
          refine ⟨3709586789080253457132833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2473057859386835638088555 3709586789080253457132833)
          ·
            refine ⟨2782190091810190092849625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3709586789080253457132833 2782190091810190092849625)
            ·
              refine ⟨2086642568857642569637219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2782190091810190092849625 2086642568857642569637219)
              ·
                refine ⟨3129963853286463854455829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2086642568857642569637219 3129963853286463854455829)
                ·
                  refine ⟨146717055622802993177617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3129963853286463854455829 146717055622802993177617)
                  ·
                    rfl

theorem cell23_2571574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_2571574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571574 prefixEnd_2571574 := by exact prefixLift 2571574
  have htrace : WordTrace (prefixWord ++ tailWord_2571574) baseStart_2571574 baseEnd_2571574 := by
    simpa [prefixWord, tailWord_2571574, baseEnd_2571574] using wordTrace_append hprefix tailTrace_2571574
  have hstable : (prefixWord ++ tailWord_2571574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571574).length < 2 ^ (prefixWord ++ tailWord_2571574).sum := by decide
  have hdescent : baseEnd_2571574 < baseStart_2571574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571576 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 2, 6, 3]
def baseStart_2571576 : Nat := 118140960795 + 2571576 * 2 ^ 59
def prefixEnd_2571576 : Nat := 4983230072969 + 3 ^ 40 * 2571576 * 2
def baseEnd_2571576 : Nat := 1320454527566535930773543

theorem tailTrace_2571576 : CollatzResearch.WordTrace tailWord_2571576 prefixEnd_2571576 1320454527566535930773543 := by
  unfold tailWord_2571576
  simp only [CollatzResearch.WordTrace]
  refine ⟨46896541065813408530095291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62528721421084544706793721 46896541065813408530095291)
  ·
    refine ⟨70344811598720112795142937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46896541065813408530095291 70344811598720112795142937)
    ·
      refine ⟨52758608699040084596357203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70344811598720112795142937 52758608699040084596357203)
      ·
        refine ⟨79137913048560126894535805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52758608699040084596357203 79137913048560126894535805)
        ·
          refine ⟨29676717393210047585450927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79137913048560126894535805 29676717393210047585450927)
          ·
            refine ⟨44515076089815071378176391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29676717393210047585450927 44515076089815071378176391)
            ·
              refine ⟨66772614134722607067264587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44515076089815071378176391 66772614134722607067264587)
              ·
                refine ⟨100158921202083910600896881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66772614134722607067264587 100158921202083910600896881)
                ·
                  refine ⟨75119190901562932950672661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100158921202083910600896881 75119190901562932950672661)
                  ·
                    refine ⟨3521212073510762482062781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 75119190901562932950672661 3521212073510762482062781)
                    ·
                      refine ⟨1320454527566535930773543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3521212073510762482062781 1320454527566535930773543)
                      ·
                        rfl

theorem cell23_2571576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 2, 6, 3].length) (baseStart_2571576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571576 prefixEnd_2571576 := by exact prefixLift 2571576
  have htrace : WordTrace (prefixWord ++ tailWord_2571576) baseStart_2571576 baseEnd_2571576 := by
    simpa [prefixWord, tailWord_2571576, baseEnd_2571576] using wordTrace_append hprefix tailTrace_2571576
  have hstable : (prefixWord ++ tailWord_2571576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571576).length < 2 ^ (prefixWord ++ tailWord_2571576).sum := by decide
  have hdescent : baseEnd_2571576 < baseStart_2571576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571596 : List Nat := [2, 2, 1, 3, 2, 2, 2, 9]
def baseStart_2571596 : Nat := 118140960795 + 2571596 * 2 ^ 59
def prefixEnd_2571596 : Nat := 4983230072969 + 3 ^ 40 * 2571596 * 2
def baseEnd_2571596 : Nat := 48906103599245401945313

theorem tailTrace_2571596 : CollatzResearch.WordTrace tailWord_2571596 prefixEnd_2571596 48906103599245401945313 := by
  unfold tailWord_2571596
  simp only [CollatzResearch.WordTrace]
  refine ⟨46896905795777180237959321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62529207727702906983945761 46896905795777180237959321)
  ·
    refine ⟨35172679346832885178469491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46896905795777180237959321 35172679346832885178469491)
    ·
      refine ⟨52759019020249327767704237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35172679346832885178469491 52759019020249327767704237)
      ·
        refine ⟨19784632132593497912889089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52759019020249327767704237 19784632132593497912889089)
        ·
          refine ⟨14838474099445123434666817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19784632132593497912889089 14838474099445123434666817)
          ·
            refine ⟨11128855574583842576000113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14838474099445123434666817 11128855574583842576000113)
            ·
              refine ⟨8346641680937881932000085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11128855574583842576000113 8346641680937881932000085)
              ·
                refine ⟨48906103599245401945313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8346641680937881932000085 48906103599245401945313)
                ·
                  rfl

theorem cell23_2571596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 9].length) (baseStart_2571596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571596 prefixEnd_2571596 := by exact prefixLift 2571596
  have htrace : WordTrace (prefixWord ++ tailWord_2571596) baseStart_2571596 baseEnd_2571596 := by
    simpa [prefixWord, tailWord_2571596, baseEnd_2571596] using wordTrace_append hprefix tailTrace_2571596
  have hstable : (prefixWord ++ tailWord_2571596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571596).length < 2 ^ (prefixWord ++ tailWord_2571596).sum := by decide
  have hdescent : baseEnd_2571596 < baseStart_2571596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571737 : List Nat := [1, 2, 1, 2, 4, 3, 3, 2, 5]
def baseStart_2571737 : Nat := 118140960795 + 2571737 * 2 ^ 59
def prefixEnd_2571737 : Nat := 4983230072969 + 3 ^ 40 * 2571737 * 2
def baseEnd_2571737 : Nat := 146726355327989977873367

theorem tailTrace_2571737 : CollatzResearch.WordTrace tailWord_2571737 prefixEnd_2571737 146726355327989977873367 := by
  unfold tailWord_2571737
  simp only [CollatzResearch.WordTrace]
  refine ⟨93798954284043541556801465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62532636189362361037867643 93798954284043541556801465)
  ·
    refine ⟨70349215713032656167601099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93798954284043541556801465 70349215713032656167601099)
    ·
      refine ⟨105523823569548984251401649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70349215713032656167601099 105523823569548984251401649)
      ·
        refine ⟨79142867677161738188551237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105523823569548984251401649 79142867677161738188551237)
        ·
          refine ⟨14839287689467825910353357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79142867677161738188551237 14839287689467825910353357)
          ·
            refine ⟨5564732883550434716382509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14839287689467825910353357 5564732883550434716382509)
            ·
              refine ⟨2086774831331413018643441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5564732883550434716382509 2086774831331413018643441)
              ·
                refine ⟨1565081123498559763982581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2086774831331413018643441 1565081123498559763982581)
                ·
                  refine ⟨146726355327989977873367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1565081123498559763982581 146726355327989977873367)
                  ·
                    rfl

theorem cell23_2571737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 2, 5].length) (baseStart_2571737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571737 prefixEnd_2571737 := by exact prefixLift 2571737
  have htrace : WordTrace (prefixWord ++ tailWord_2571737) baseStart_2571737 baseEnd_2571737 := by
    simpa [prefixWord, tailWord_2571737, baseEnd_2571737] using wordTrace_append hprefix tailTrace_2571737
  have hstable : (prefixWord ++ tailWord_2571737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571737).length < 2 ^ (prefixWord ++ tailWord_2571737).sum := by decide
  have hdescent : baseEnd_2571737 < baseStart_2571737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571743 : List Nat := [1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 5]
def baseStart_2571743 : Nat := 118140960795 + 2571743 * 2 ^ 59
def prefixEnd_2571743 : Nat := 4983230072969 + 3 ^ 40 * 2571743 * 2
def baseEnd_2571743 : Nat := 1320540278835836777385275

theorem tailTrace_2571743 : CollatzResearch.WordTrace tailWord_2571743 prefixEnd_2571743 1320540278835836777385275 := by
  unfold tailWord_2571743
  simp only [CollatzResearch.WordTrace]
  refine ⟨93799173122021804581519883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62532782081347869721013255 93799173122021804581519883)
  ·
    refine ⟨140698759683032706872279825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93799173122021804581519883 140698759683032706872279825)
    ·
      refine ⟨105524069762274530154209869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140698759683032706872279825 105524069762274530154209869)
      ·
        refine ⟨39571526160852948807828701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105524069762274530154209869 39571526160852948807828701)
        ·
          refine ⟨14839322310319855802935763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39571526160852948807828701 14839322310319855802935763)
          ·
            refine ⟨22258983465479783704403645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14839322310319855802935763 22258983465479783704403645)
            ·
              refine ⟨8347118799554918889151367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22258983465479783704403645 8347118799554918889151367)
              ·
                refine ⟨12520678199332378333727051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8347118799554918889151367 12520678199332378333727051)
                ·
                  refine ⟨18781017298998567500590577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12520678199332378333727051 18781017298998567500590577)
                  ·
                    refine ⟨14085762974248925625442933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18781017298998567500590577 14085762974248925625442933)
                    ·
                      refine ⟨1320540278835836777385275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14085762974248925625442933 1320540278835836777385275)
                      ·
                        rfl

theorem cell23_2571743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_2571743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571743 prefixEnd_2571743 := by exact prefixLift 2571743
  have htrace : WordTrace (prefixWord ++ tailWord_2571743) baseStart_2571743 baseEnd_2571743 := by
    simpa [prefixWord, tailWord_2571743, baseEnd_2571743] using wordTrace_append hprefix tailTrace_2571743
  have hstable : (prefixWord ++ tailWord_2571743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571743).length < 2 ^ (prefixWord ++ tailWord_2571743).sum := by decide
  have hdescent : baseEnd_2571743 < baseStart_2571743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571770 : List Nat := [3, 1, 1, 1, 1, 2, 6, 1, 2, 1, 4]
def baseStart_2571770 : Nat := 118140960795 + 2571770 * 2 ^ 59
def prefixEnd_2571770 : Nat := 4983230072969 + 3 ^ 40 * 2571770 * 2
def baseEnd_2571770 : Nat := 1320554142813508171747651

theorem tailTrace_2571770 : CollatzResearch.WordTrace tailWord_2571770 prefixEnd_2571770 1320554142813508171747651 := by
  unfold tailWord_2571770
  simp only [CollatzResearch.WordTrace]
  refine ⟨23450039473230997048188191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62533438595282658795168509 23450039473230997048188191)
  ·
    refine ⟨35175059209846495572282287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23450039473230997048188191 35175059209846495572282287)
    ·
      refine ⟨52762588814769743358423431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35175059209846495572282287 52762588814769743358423431)
      ·
        refine ⟨79143883222154615037635147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52762588814769743358423431 79143883222154615037635147)
        ·
          refine ⟨118715824833231922556452721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79143883222154615037635147 118715824833231922556452721)
          ·
            refine ⟨89036868624923941917339541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118715824833231922556452721 89036868624923941917339541)
            ·
              refine ⟨4173603216793309777375291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 89036868624923941917339541 4173603216793309777375291)
              ·
                refine ⟨6260404825189964666062937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4173603216793309777375291 6260404825189964666062937)
                ·
                  refine ⟨4695303618892473499547203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6260404825189964666062937 4695303618892473499547203)
                  ·
                    refine ⟨7042955428338710249320805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4695303618892473499547203 7042955428338710249320805)
                    ·
                      refine ⟨1320554142813508171747651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7042955428338710249320805 1320554142813508171747651)
                      ·
                        rfl

theorem cell23_2571770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 2, 1, 4].length) (baseStart_2571770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571770 prefixEnd_2571770 := by exact prefixLift 2571770
  have htrace : WordTrace (prefixWord ++ tailWord_2571770) baseStart_2571770 baseEnd_2571770 := by
    simpa [prefixWord, tailWord_2571770, baseEnd_2571770] using wordTrace_append hprefix tailTrace_2571770
  have hstable : (prefixWord ++ tailWord_2571770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571770).length < 2 ^ (prefixWord ++ tailWord_2571770).sum := by decide
  have hdescent : baseEnd_2571770 < baseStart_2571770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571810 : List Nat := [3, 3, 1, 1, 1, 1, 4, 3, 6]
def baseStart_2571810 : Nat := 118140960795 + 2571810 * 2 ^ 59
def prefixEnd_2571810 : Nat := 4983230072969 + 3 ^ 40 * 2571810 * 2
def baseEnd_2571810 : Nat := 146730520226632001694163

theorem tailTrace_2571810 : CollatzResearch.WordTrace tailWord_2571810 prefixEnd_2571810 146730520226632001694163 := by
  unfold tailWord_2571810
  simp only [CollatzResearch.WordTrace]
  refine ⟨23450404203194768756052221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62534411208519383349472589 23450404203194768756052221)
  ·
    refine ⟨8793901576198038283519583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23450404203194768756052221 8793901576198038283519583)
    ·
      refine ⟨13190852364297057425279375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8793901576198038283519583 13190852364297057425279375)
      ·
        refine ⟨19786278546445586137919063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13190852364297057425279375 19786278546445586137919063)
        ·
          refine ⟨29679417819668379206878595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19786278546445586137919063 29679417819668379206878595)
          ·
            refine ⟨44519126729502568810317893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29679417819668379206878595 44519126729502568810317893)
            ·
              refine ⟨8347336261781731651934605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44519126729502568810317893 8347336261781731651934605)
              ·
                refine ⟨3130251098168149369475477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8347336261781731651934605 3130251098168149369475477)
                ·
                  refine ⟨146730520226632001694163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3130251098168149369475477 146730520226632001694163)
                  ·
                    rfl

theorem cell23_2571810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_2571810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571810 prefixEnd_2571810 := by exact prefixLift 2571810
  have htrace : WordTrace (prefixWord ++ tailWord_2571810) baseStart_2571810 baseEnd_2571810 := by
    simpa [prefixWord, tailWord_2571810, baseEnd_2571810] using wordTrace_append hprefix tailTrace_2571810
  have hstable : (prefixWord ++ tailWord_2571810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571810).length < 2 ^ (prefixWord ++ tailWord_2571810).sum := by decide
  have hdescent : baseEnd_2571810 < baseStart_2571810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571877 : List Nat := [1, 3, 1, 3, 3, 1, 1, 4, 1, 1, 4]
def baseStart_2571877 : Nat := 118140960795 + 2571877 * 2 ^ 59
def prefixEnd_2571877 : Nat := 4983230072969 + 3 ^ 40 * 2571877 * 2
def baseEnd_2571877 : Nat := 1320609085243539253109659

theorem tailTrace_2571877 : CollatzResearch.WordTrace tailWord_2571877 prefixEnd_2571877 1320609085243539253109659 := by
  unfold tailWord_2571877
  simp only [CollatzResearch.WordTrace]
  refine ⟨93804060503536345466897885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62536040335690896977931923 93804060503536345466897885)
  ·
    refine ⟨35176522688826129550086707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93804060503536345466897885 35176522688826129550086707)
    ·
      refine ⟨52764784033239194325130061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35176522688826129550086707 52764784033239194325130061)
      ·
        refine ⟨19786794012464697871923773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52764784033239194325130061 19786794012464697871923773)
        ·
          refine ⟨7420047754674261701971415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19786794012464697871923773 7420047754674261701971415)
          ·
            refine ⟨11130071632011392552957123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7420047754674261701971415 11130071632011392552957123)
            ·
              refine ⟨16695107448017088829435685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11130071632011392552957123 16695107448017088829435685)
              ·
                refine ⟨3130332646503204155519191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16695107448017088829435685 3130332646503204155519191)
                ·
                  refine ⟨4695498969754806233278787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3130332646503204155519191 4695498969754806233278787)
                  ·
                    refine ⟨7043248454632209349918181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4695498969754806233278787 7043248454632209349918181)
                    ·
                      refine ⟨1320609085243539253109659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7043248454632209349918181 1320609085243539253109659)
                      ·
                        rfl

theorem cell23_2571877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_2571877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571877 prefixEnd_2571877 := by exact prefixLift 2571877
  have htrace : WordTrace (prefixWord ++ tailWord_2571877) baseStart_2571877 baseEnd_2571877 := by
    simpa [prefixWord, tailWord_2571877, baseEnd_2571877] using wordTrace_append hprefix tailTrace_2571877
  have hstable : (prefixWord ++ tailWord_2571877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571877).length < 2 ^ (prefixWord ++ tailWord_2571877).sum := by decide
  have hdescent : baseEnd_2571877 < baseStart_2571877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571894 : List Nat := [5, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4]
def baseStart_2571894 : Nat := 118140960795 + 2571894 * 2 ^ 59
def prefixEnd_2571894 : Nat := 4983230072969 + 3 ^ 40 * 2571894 * 2
def baseEnd_2571894 : Nat := 1320617814414665686597081

theorem tailTrace_2571894 : CollatzResearch.WordTrace tailWord_2571894 prefixEnd_2571894 1320617814414665686597081 := by
  unfold tailWord_2571894
  simp only [CollatzResearch.WordTrace]
  refine ⟨5862792534029672335641671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62536453696316504913511157 5862792534029672335641671)
  ·
    refine ⟨8794188801044508503462507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5862792534029672335641671 8794188801044508503462507)
    ·
      refine ⟨13191283201566762755193761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8794188801044508503462507 13191283201566762755193761)
      ·
        refine ⟨9893462401175072066395321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13191283201566762755193761 9893462401175072066395321)
        ·
          refine ⟨7420096800881304049796491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9893462401175072066395321 7420096800881304049796491)
          ·
            refine ⟨11130145201321956074694737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7420096800881304049796491 11130145201321956074694737)
            ·
              refine ⟨8347608900991467056021053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11130145201321956074694737 8347608900991467056021053)
              ·
                refine ⟨3130353337871800146007895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8347608900991467056021053 3130353337871800146007895)
                ·
                  refine ⟨4695530006807700219011843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3130353337871800146007895 4695530006807700219011843)
                  ·
                    refine ⟨7043295010211550328517765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4695530006807700219011843 7043295010211550328517765)
                    ·
                      refine ⟨1320617814414665686597081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7043295010211550328517765 1320617814414665686597081)
                      ·
                        rfl

theorem cell23_2571894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_2571894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571894 prefixEnd_2571894 := by exact prefixLift 2571894
  have htrace : WordTrace (prefixWord ++ tailWord_2571894) baseStart_2571894 baseEnd_2571894 := by
    simpa [prefixWord, tailWord_2571894, baseEnd_2571894] using wordTrace_append hprefix tailTrace_2571894
  have hstable : (prefixWord ++ tailWord_2571894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571894).length < 2 ^ (prefixWord ++ tailWord_2571894).sum := by decide
  have hdescent : baseEnd_2571894 < baseStart_2571894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571897 : List Nat := [1, 2, 1, 3, 3, 1, 1, 5, 1, 2, 3]
def baseStart_2571897 : Nat := 118140960795 + 2571897 * 2 ^ 59
def prefixEnd_2571897 : Nat := 4983230072969 + 3 ^ 40 * 2571897 * 2
def baseEnd_2571897 : Nat := 1320619354856629174859567

theorem tailTrace_2571897 : CollatzResearch.WordTrace tailWord_2571897 prefixEnd_2571897 1320619354856629174859567 := by
  unfold tailWord_2571897
  simp only [CollatzResearch.WordTrace]
  refine ⟨93804789963463888882625945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62536526642309259255083963 93804789963463888882625945)
  ·
    refine ⟨70353592472597916661969459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93804789963463888882625945 70353592472597916661969459)
    ·
      refine ⟨105530388708896874992954189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70353592472597916661969459 105530388708896874992954189)
      ·
        refine ⟨39573895765836328122357821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105530388708896874992954189 39573895765836328122357821)
        ·
          refine ⟨14840210912188623045884183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39573895765836328122357821 14840210912188623045884183)
          ·
            refine ⟨22260316368282934568826275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14840210912188623045884183 22260316368282934568826275)
            ·
              refine ⟨33390474552424401853239413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22260316368282934568826275 33390474552424401853239413)
              ·
                refine ⟨3130356989289787673741195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33390474552424401853239413 3130356989289787673741195)
                ·
                  refine ⟨4695535483934681510611793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3130356989289787673741195 4695535483934681510611793)
                  ·
                    refine ⟨3521651612951011132958845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4695535483934681510611793 3521651612951011132958845)
                    ·
                      refine ⟨1320619354856629174859567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3521651612951011132958845 1320619354856629174859567)
                      ·
                        rfl

theorem cell23_2571897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_2571897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571897 prefixEnd_2571897 := by exact prefixLift 2571897
  have htrace : WordTrace (prefixWord ++ tailWord_2571897) baseStart_2571897 baseEnd_2571897 := by
    simpa [prefixWord, tailWord_2571897, baseEnd_2571897] using wordTrace_append hprefix tailTrace_2571897
  have hstable : (prefixWord ++ tailWord_2571897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571897).length < 2 ^ (prefixWord ++ tailWord_2571897).sum := by decide
  have hdescent : baseEnd_2571897 < baseStart_2571897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571911 : List Nat := [1, 1, 4, 2, 1, 5, 1, 1, 3, 2, 2]
def baseStart_2571911 : Nat := 118140960795 + 2571911 * 2 ^ 59
def prefixEnd_2571911 : Nat := 4983230072969 + 3 ^ 40 * 2571911 * 2
def baseEnd_2571911 : Nat := 1320626543585792120084503

theorem tailTrace_2571911 : CollatzResearch.WordTrace tailWord_2571911 prefixEnd_2571911 1320626543585792120084503 := by
  unfold tailWord_2571911
  simp only [CollatzResearch.WordTrace]
  refine ⟨93805300585413169273635587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62536867056942112849090391 93805300585413169273635587)
  ·
    refine ⟨140707950878119753910453381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93805300585413169273635587 140707950878119753910453381)
    ·
      refine ⟨26382740789647453858210009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140707950878119753910453381 26382740789647453858210009)
      ·
        refine ⟨19787055592235590393657507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26382740789647453858210009 19787055592235590393657507)
        ·
          refine ⟨29680583388353385590486261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19787055592235590393657507 29680583388353385590486261)
          ·
            refine ⟨2782554692658129899108087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29680583388353385590486261 2782554692658129899108087)
            ·
              refine ⟨4173832038987194848662131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2782554692658129899108087 4173832038987194848662131)
              ·
                refine ⟨6260748058480792272993197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4173832038987194848662131 6260748058480792272993197)
                ·
                  refine ⟨2347780521930297102372449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6260748058480792272993197 2347780521930297102372449)
                  ·
                    refine ⟨1760835391447722826779337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2347780521930297102372449 1760835391447722826779337)
                    ·
                      refine ⟨1320626543585792120084503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1760835391447722826779337 1320626543585792120084503)
                      ·
                        rfl

theorem cell23_2571911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_2571911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571911 prefixEnd_2571911 := by exact prefixLift 2571911
  have htrace : WordTrace (prefixWord ++ tailWord_2571911) baseStart_2571911 baseEnd_2571911 := by
    simpa [prefixWord, tailWord_2571911, baseEnd_2571911] using wordTrace_append hprefix tailTrace_2571911
  have hstable : (prefixWord ++ tailWord_2571911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571911).length < 2 ^ (prefixWord ++ tailWord_2571911).sum := by decide
  have hdescent : baseEnd_2571911 < baseStart_2571911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571954 : List Nat := [3, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2]
def baseStart_2571954 : Nat := 118140960795 + 2571954 * 2 ^ 59
def prefixEnd_2571954 : Nat := 4983230072969 + 3 ^ 40 * 2571954 * 2
def baseEnd_2571954 : Nat := 1320648623253935451846805

theorem tailTrace_2571954 : CollatzResearch.WordTrace tailWord_2571954 prefixEnd_2571954 1320648623253935451846805 := by
  unfold tailWord_2571954
  simp only [CollatzResearch.WordTrace]
  refine ⟨23451717231064346904362729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62537912616171591744967277 23451717231064346904362729)
  ·
    refine ⟨17588787923298260178272047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23451717231064346904362729 17588787923298260178272047)
    ·
      refine ⟨26383181884947390267408071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17588787923298260178272047 26383181884947390267408071)
      ·
        refine ⟨39574772827421085401112107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26383181884947390267408071 39574772827421085401112107)
        ·
          refine ⟨59362159241131628101668161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39574772827421085401112107 59362159241131628101668161)
          ·
            refine ⟨44521619430848721076251121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59362159241131628101668161 44521619430848721076251121)
            ·
              refine ⟨33391214573136540807188341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44521619430848721076251121 33391214573136540807188341)
              ·
                refine ⟨3130426366231550700673907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33391214573136540807188341 3130426366231550700673907)
                ·
                  refine ⟨4695639549347326051010861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3130426366231550700673907 4695639549347326051010861)
                  ·
                    refine ⟨1760864831005247269129073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4695639549347326051010861 1760864831005247269129073)
                    ·
                      refine ⟨1320648623253935451846805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1760864831005247269129073 1320648623253935451846805)
                      ·
                        rfl

theorem cell23_2571954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2].length) (baseStart_2571954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571954 prefixEnd_2571954 := by exact prefixLift 2571954
  have htrace : WordTrace (prefixWord ++ tailWord_2571954) baseStart_2571954 baseEnd_2571954 := by
    simpa [prefixWord, tailWord_2571954, baseEnd_2571954] using wordTrace_append hprefix tailTrace_2571954
  have hstable : (prefixWord ++ tailWord_2571954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571954).length < 2 ^ (prefixWord ++ tailWord_2571954).sum := by decide
  have hdescent : baseEnd_2571954 < baseStart_2571954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2571967 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 3, 4, 2]
def baseStart_2571967 : Nat := 118140960795 + 2571967 * 2 ^ 59
def prefixEnd_2571967 : Nat := 4983230072969 + 3 ^ 40 * 2571967 * 2
def baseEnd_2571967 : Nat := 1320655298502443900984245

theorem tailTrace_2571967 : CollatzResearch.WordTrace tailWord_2571967 prefixEnd_2571967 1320655298502443900984245 := by
  unfold tailWord_2571967
  simp only [CollatzResearch.WordTrace]
  refine ⟨93807343073210290837674155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62538228715473527225116103 93807343073210290837674155)
  ·
    refine ⟨140711014609815436256511233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93807343073210290837674155 140711014609815436256511233)
    ·
      refine ⟨105533260957361577192383425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140711014609815436256511233 105533260957361577192383425)
      ·
        refine ⟨79149945718021182894287569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105533260957361577192383425 79149945718021182894287569)
        ·
          refine ⟨59362459288515887170715677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79149945718021182894287569 59362459288515887170715677)
          ·
            refine ⟨22260922233193457689018379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59362459288515887170715677 22260922233193457689018379)
            ·
              refine ⟨33391383349790186533527569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22260922233193457689018379 33391383349790186533527569)
              ·
                refine ⟨25043537512342639900145677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33391383349790186533527569 25043537512342639900145677)
                ·
                  refine ⟨9391326567128489962554629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25043537512342639900145677 9391326567128489962554629)
                  ·
                    refine ⟨1760873731336591867978993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9391326567128489962554629 1760873731336591867978993)
                    ·
                      refine ⟨1320655298502443900984245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1760873731336591867978993 1320655298502443900984245)
                      ·
                        rfl

theorem cell23_2571967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 4, 2].length) (baseStart_2571967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2571967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2571967 prefixEnd_2571967 := by exact prefixLift 2571967
  have htrace : WordTrace (prefixWord ++ tailWord_2571967) baseStart_2571967 baseEnd_2571967 := by
    simpa [prefixWord, tailWord_2571967, baseEnd_2571967] using wordTrace_append hprefix tailTrace_2571967
  have hstable : (prefixWord ++ tailWord_2571967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2571967).length < 2 ^ (prefixWord ++ tailWord_2571967).sum := by decide
  have hdescent : baseEnd_2571967 < baseStart_2571967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2571967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572017 : List Nat := [1, 2, 2, 2, 2, 3, 1, 2, 2, 3, 3]
def baseStart_2572017 : Nat := 118140960795 + 2572017 * 2 ^ 59
def prefixEnd_2572017 : Nat := 4983230072969 + 3 ^ 40 * 2572017 * 2
def baseEnd_2572017 : Nat := 1320680972535168705359015

theorem tailTrace_2572017 : CollatzResearch.WordTrace tailWord_2572017 prefixEnd_2572017 1320680972535168705359015 := by
  unfold tailWord_2572017
  simp only [CollatzResearch.WordTrace]
  refine ⟨93809166723029149376994305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62539444482019432917996203 93809166723029149376994305)
  ·
    refine ⟨70356875042271862032745729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93809166723029149376994305 70356875042271862032745729)
    ·
      refine ⟨52767656281703896524559297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70356875042271862032745729 52767656281703896524559297)
      ·
        refine ⟨39575742211277922393419473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52767656281703896524559297 39575742211277922393419473)
        ·
          refine ⟨29681806658458441795064605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39575742211277922393419473 29681806658458441795064605)
          ·
            refine ⟨11130677496921915673149227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29681806658458441795064605 11130677496921915673149227)
            ·
              refine ⟨16696016245382873509723841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11130677496921915673149227 16696016245382873509723841)
              ·
                refine ⟨12522012184037155132292881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16696016245382873509723841 12522012184037155132292881)
                ·
                  refine ⟨9391509138027866349219661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12522012184037155132292881 9391509138027866349219661)
                  ·
                    refine ⟨3521815926760449880957373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9391509138027866349219661 3521815926760449880957373)
                    ·
                      refine ⟨1320680972535168705359015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3521815926760449880957373 1320680972535168705359015)
                      ·
                        rfl

theorem cell23_2572017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_2572017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572017 prefixEnd_2572017 := by exact prefixLift 2572017
  have htrace : WordTrace (prefixWord ++ tailWord_2572017) baseStart_2572017 baseEnd_2572017 := by
    simpa [prefixWord, tailWord_2572017, baseEnd_2572017] using wordTrace_append hprefix tailTrace_2572017
  have hstable : (prefixWord ++ tailWord_2572017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572017).length < 2 ^ (prefixWord ++ tailWord_2572017).sum := by decide
  have hdescent : baseEnd_2572017 < baseStart_2572017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572027 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 2, 5, 2]
def baseStart_2572027 : Nat := 118140960795 + 2572027 * 2 ^ 59
def prefixEnd_2572027 : Nat := 4983230072969 + 3 ^ 40 * 2572027 * 2
def baseEnd_2572027 : Nat := 1320686107341713666233969

theorem tailTrace_2572027 : CollatzResearch.WordTrace tailWord_2572027 prefixEnd_2572027 1320686107341713666233969 := by
  unfold tailWord_2572027
  simp only [CollatzResearch.WordTrace]
  refine ⟨93809531452992921084858335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62539687635328614056572223 93809531452992921084858335)
  ·
    refine ⟨140714297179489381627287503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93809531452992921084858335 140714297179489381627287503)
    ·
      refine ⟨211071445769234072440931255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140714297179489381627287503 211071445769234072440931255)
      ·
        refine ⟨316607168653851108661396883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211071445769234072440931255 316607168653851108661396883)
        ·
          refine ⟨474910752980776662992095325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316607168653851108661396883 474910752980776662992095325)
          ·
            refine ⟨178091532367791248622035747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 474910752980776662992095325 178091532367791248622035747)
            ·
              refine ⟨267137298551686872933053621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178091532367791248622035747 267137298551686872933053621)
              ·
                refine ⟨25044121739220644337473777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 267137298551686872933053621 25044121739220644337473777)
                ·
                  refine ⟨18783091304415483253105333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25044121739220644337473777 18783091304415483253105333)
                  ·
                    refine ⟨1760914809788951554978625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18783091304415483253105333 1760914809788951554978625)
                    ·
                      refine ⟨1320686107341713666233969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1760914809788951554978625 1320686107341713666233969)
                      ·
                        rfl

theorem cell23_2572027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 5, 2].length) (baseStart_2572027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572027 prefixEnd_2572027 := by exact prefixLift 2572027
  have htrace : WordTrace (prefixWord ++ tailWord_2572027) baseStart_2572027 baseEnd_2572027 := by
    simpa [prefixWord, tailWord_2572027, baseEnd_2572027] using wordTrace_append hprefix tailTrace_2572027
  have hstable : (prefixWord ++ tailWord_2572027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572027).length < 2 ^ (prefixWord ++ tailWord_2572027).sum := by decide
  have hdescent : baseEnd_2572027 < baseStart_2572027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572034 : List Nat := [3, 4, 1, 1, 1, 1, 1, 3, 2, 3, 3]
def baseStart_2572034 : Nat := 118140960795 + 2572034 * 2 ^ 59
def prefixEnd_2572034 : Nat := 4983230072969 + 3 ^ 40 * 2572034 * 2
def baseEnd_2572034 : Nat := 1320689701706295138846437

theorem tailTrace_2572034 : CollatzResearch.WordTrace tailWord_2572034 prefixEnd_2572034 1320689701706295138846437 := by
  unfold tailWord_2572034
  simp only [CollatzResearch.WordTrace]
  refine ⟨23452446690991890320090789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62539857842645040853575437 23452446690991890320090789)
  ·
    refine ⟨4397333754560979435017023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23452446690991890320090789 4397333754560979435017023)
    ·
      refine ⟨6596000631841469152525535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4397333754560979435017023 6596000631841469152525535)
      ·
        refine ⟨9894000947762203728788303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6596000631841469152525535 9894000947762203728788303)
        ·
          refine ⟨14841001421643305593182455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9894000947762203728788303 14841001421643305593182455)
          ·
            refine ⟨22261502132464958389773683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14841001421643305593182455 22261502132464958389773683)
            ·
              refine ⟨33392253198697437584660525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22261502132464958389773683 33392253198697437584660525)
              ·
                refine ⟨12522094949511539094247697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33392253198697437584660525 12522094949511539094247697)
                ·
                  refine ⟨9391571212133654320685773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12522094949511539094247697 9391571212133654320685773)
                  ·
                    refine ⟨3521839204550120370257165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9391571212133654320685773 3521839204550120370257165)
                    ·
                      refine ⟨1320689701706295138846437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3521839204550120370257165 1320689701706295138846437)
                      ·
                        rfl

theorem cell23_2572034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_2572034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572034 prefixEnd_2572034 := by exact prefixLift 2572034
  have htrace : WordTrace (prefixWord ++ tailWord_2572034) baseStart_2572034 baseEnd_2572034 := by
    simpa [prefixWord, tailWord_2572034, baseEnd_2572034] using wordTrace_append hprefix tailTrace_2572034
  have hstable : (prefixWord ++ tailWord_2572034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572034).length < 2 ^ (prefixWord ++ tailWord_2572034).sum := by decide
  have hdescent : baseEnd_2572034 < baseStart_2572034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572067 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 5, 4]
def baseStart_2572067 : Nat := 118140960795 + 2572067 * 2 ^ 59
def prefixEnd_2572067 : Nat := 4983230072969 + 3 ^ 40 * 2572067 * 2
def baseEnd_2572067 : Nat := 440235548855964503244595

theorem tailTrace_2572067 : CollatzResearch.WordTrace tailWord_2572067 prefixEnd_2572067 440235548855964503244595 := by
  unfold tailWord_2572067
  simp only [CollatzResearch.WordTrace]
  refine ⟨93810990372848007916314455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62540660248565338610876303 93810990372848007916314455)
  ·
    refine ⟨140716485559272011874471683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93810990372848007916314455 140716485559272011874471683)
    ·
      refine ⟨211074728338908017811707525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140716485559272011874471683 211074728338908017811707525)
      ·
        refine ⟨39576511563545253339695161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 211074728338908017811707525 39576511563545253339695161)
        ·
          refine ⟨29682383672658940004771371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39576511563545253339695161 29682383672658940004771371)
          ·
            refine ⟨44523575508988410007157057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29682383672658940004771371 44523575508988410007157057)
            ·
              refine ⟨33392681631741307505367793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44523575508988410007157057 33392681631741307505367793)
              ·
                refine ⟨25044511223805980629025845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33392681631741307505367793 25044511223805980629025845)
                ·
                  refine ⟨2347922927231810683971173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25044511223805980629025845 2347922927231810683971173)
                  ·
                    refine ⟨440235548855964503244595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2347922927231810683971173 440235548855964503244595)
                    ·
                      rfl

theorem cell23_2572067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 5, 4].length) (baseStart_2572067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572067 prefixEnd_2572067 := by exact prefixLift 2572067
  have htrace : WordTrace (prefixWord ++ tailWord_2572067) baseStart_2572067 baseEnd_2572067 := by
    simpa [prefixWord, tailWord_2572067, baseEnd_2572067] using wordTrace_append hprefix tailTrace_2572067
  have hstable : (prefixWord ++ tailWord_2572067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572067).length < 2 ^ (prefixWord ++ tailWord_2572067).sum := by decide
  have hdescent : baseEnd_2572067 < baseStart_2572067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572158 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_2572158 : Nat := 118140960795 + 2572158 * 2 ^ 59
def prefixEnd_2572158 : Nat := 4983230072969 + 3 ^ 40 * 2572158 * 2
def baseEnd_2572158 : Nat := 1320753373307452653695867

theorem tailTrace_2572158 : CollatzResearch.WordTrace tailWord_2572158 prefixEnd_2572158 1320753373307452653695867 := by
  unfold tailWord_2572158
  simp only [CollatzResearch.WordTrace]
  refine ⟨11726788676939791307234641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 62542872943678886971918085 11726788676939791307234641)
  ·
    refine ⟨8795091507704843480425981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11726788676939791307234641 8795091507704843480425981)
    ·
      refine ⟨3298159315389316305159743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8795091507704843480425981 3298159315389316305159743)
      ·
        refine ⟨4947238973083974457739615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3298159315389316305159743 4947238973083974457739615)
        ·
          refine ⟨7420858459625961686609423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4947238973083974457739615 7420858459625961686609423)
          ·
            refine ⟨11131287689438942529914135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7420858459625961686609423 11131287689438942529914135)
            ·
              refine ⟨16696931534158413794871203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11131287689438942529914135 16696931534158413794871203)
              ·
                refine ⟨25045397301237620692306805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16696931534158413794871203 25045397301237620692306805)
                ·
                  refine ⟨2348005996991026939903763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25045397301237620692306805 2348005996991026939903763)
                  ·
                    refine ⟨3522008995486540409855645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2348005996991026939903763 3522008995486540409855645)
                    ·
                      refine ⟨1320753373307452653695867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3522008995486540409855645 1320753373307452653695867)
                      ·
                        rfl

theorem cell23_2572158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_2572158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572158 prefixEnd_2572158 := by exact prefixLift 2572158
  have htrace : WordTrace (prefixWord ++ tailWord_2572158) baseStart_2572158 baseEnd_2572158 := by
    simpa [prefixWord, tailWord_2572158, baseEnd_2572158] using wordTrace_append hprefix tailTrace_2572158
  have hstable : (prefixWord ++ tailWord_2572158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572158).length < 2 ^ (prefixWord ++ tailWord_2572158).sum := by decide
  have hdescent : baseEnd_2572158 < baseStart_2572158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572164 : List Nat := [2, 3, 2, 1, 1, 1, 4, 1, 3, 1, 4]
def baseStart_2572164 : Nat := 118140960795 + 2572164 * 2 ^ 59
def prefixEnd_2572164 : Nat := 4983230072969 + 3 ^ 40 * 2572164 * 2
def baseEnd_2572164 : Nat := 1320756454191379630220839

theorem tailTrace_2572164 : CollatzResearch.WordTrace tailWord_2572164 prefixEnd_2572164 1320756454191379630220839 := by
  unfold tailWord_2572164
  simp only [CollatzResearch.WordTrace]
  refine ⟨46907264126748296741297773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62543018835664395655063697 46907264126748296741297773)
  ·
    refine ⟨17590224047530611277986665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46907264126748296741297773 17590224047530611277986665)
    ·
      refine ⟨13192668035647958458489999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17590224047530611277986665 13192668035647958458489999)
      ·
        refine ⟨19789002053471937687734999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13192668035647958458489999 19789002053471937687734999)
        ·
          refine ⟨29683503080207906531602499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19789002053471937687734999 29683503080207906531602499)
          ·
            refine ⟨44525254620311859797403749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29683503080207906531602499 44525254620311859797403749)
            ·
              refine ⟨8348485241308473712013203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44525254620311859797403749 8348485241308473712013203)
              ·
                refine ⟨12522727861962710568019805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8348485241308473712013203 12522727861962710568019805)
                ·
                  refine ⟨4696022948236016463007427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12522727861962710568019805 4696022948236016463007427)
                  ·
                    refine ⟨7044034422354024694511141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4696022948236016463007427 7044034422354024694511141)
                    ·
                      refine ⟨1320756454191379630220839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7044034422354024694511141 1320756454191379630220839)
                      ·
                        rfl

theorem cell23_2572164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_2572164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572164 prefixEnd_2572164 := by exact prefixLift 2572164
  have htrace : WordTrace (prefixWord ++ tailWord_2572164) baseStart_2572164 baseEnd_2572164 := by
    simpa [prefixWord, tailWord_2572164, baseEnd_2572164] using wordTrace_append hprefix tailTrace_2572164
  have hstable : (prefixWord ++ tailWord_2572164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572164).length < 2 ^ (prefixWord ++ tailWord_2572164).sum := by decide
  have hdescent : baseEnd_2572164 < baseStart_2572164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572178 : List Nat := [3, 2, 3, 2, 1, 1, 4, 1, 1, 5]
def baseStart_2572178 : Nat := 118140960795 + 2572178 * 2 ^ 59
def prefixEnd_2572178 : Nat := 4983230072969 + 3 ^ 40 * 2572178 * 2
def baseEnd_2572178 : Nat := 440254547640180858481925

theorem tailTrace_2572178 : CollatzResearch.WordTrace tailWord_2572178 prefixEnd_2572178 440254547640180858481925 := by
  unfold tailWord_2572178
  simp only [CollatzResearch.WordTrace]
  refine ⟨23453759718861468468401297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 62543359250297249249070125 23453759718861468468401297)
  ·
    refine ⟨17590319789146101351300973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23453759718861468468401297 17590319789146101351300973)
    ·
      refine ⟨6596369920929788006737865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17590319789146101351300973 6596369920929788006737865)
      ·
        refine ⟨4947277440697341005053399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6596369920929788006737865 4947277440697341005053399)
        ·
          refine ⟨7420916161046011507580099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4947277440697341005053399 7420916161046011507580099)
          ·
            refine ⟨11131374241569017261370149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7420916161046011507580099 11131374241569017261370149)
            ·
              refine ⟨2087132670294190736506903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11131374241569017261370149 2087132670294190736506903)
              ·
                refine ⟨3130699005441286104760355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2087132670294190736506903 3130699005441286104760355)
                ·
                  refine ⟨4696048508161929157140533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3130699005441286104760355 4696048508161929157140533)
                  ·
                    refine ⟨440254547640180858481925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4696048508161929157140533 440254547640180858481925)
                    ·
                      rfl

theorem cell23_2572178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_2572178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572178 prefixEnd_2572178 := by exact prefixLift 2572178
  have htrace : WordTrace (prefixWord ++ tailWord_2572178) baseStart_2572178 baseEnd_2572178 := by
    simpa [prefixWord, tailWord_2572178, baseEnd_2572178] using wordTrace_append hprefix tailTrace_2572178
  have hstable : (prefixWord ++ tailWord_2572178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572178).length < 2 ^ (prefixWord ++ tailWord_2572178).sum := by decide
  have hdescent : baseEnd_2572178 < baseStart_2572178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572181 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 5, 2, 2]
def baseStart_2572181 : Nat := 118140960795 + 2572181 * 2 ^ 59
def prefixEnd_2572181 : Nat := 4983230072969 + 3 ^ 40 * 2572181 * 2
def baseEnd_2572181 : Nat := 1320765183362506063708261

theorem tailTrace_2572181 : CollatzResearch.WordTrace tailWord_2572181 prefixEnd_2572181 1320765183362506063708261 := by
  unfold tailWord_2572181
  simp only [CollatzResearch.WordTrace]
  refine ⟨93815148294435005385964397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62543432196290003590642931 93815148294435005385964397)
  ·
    refine ⟨35180680610413127019736649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93815148294435005385964397 35180680610413127019736649)
    ·
      refine ⟨26385510457809845264802487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35180680610413127019736649 26385510457809845264802487)
      ·
        refine ⟨39578265686714767897203731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26385510457809845264802487 39578265686714767897203731)
        ·
          refine ⟨59367398530072151845805597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39578265686714767897203731 59367398530072151845805597)
          ·
            refine ⟨22262774448777056942177099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59367398530072151845805597 22262774448777056942177099)
            ·
              refine ⟨33394161673165585413265649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22262774448777056942177099 33394161673165585413265649)
              ·
                refine ⟨25045621254874189059949237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33394161673165585413265649 25045621254874189059949237)
                ·
                  refine ⟨2348026992644455224370241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25045621254874189059949237 2348026992644455224370241)
                  ·
                    refine ⟨1761020244483341418277681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2348026992644455224370241 1761020244483341418277681)
                    ·
                      refine ⟨1320765183362506063708261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1761020244483341418277681 1320765183362506063708261)
                      ·
                        rfl

theorem cell23_2572181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 5, 2, 2].length) (baseStart_2572181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572181 prefixEnd_2572181 := by exact prefixLift 2572181
  have htrace : WordTrace (prefixWord ++ tailWord_2572181) baseStart_2572181 baseEnd_2572181 := by
    simpa [prefixWord, tailWord_2572181, baseEnd_2572181] using wordTrace_append hprefix tailTrace_2572181
  have hstable : (prefixWord ++ tailWord_2572181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572181).length < 2 ^ (prefixWord ++ tailWord_2572181).sum := by decide
  have hdescent : baseEnd_2572181 < baseStart_2572181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572182 : List Nat := [5, 3, 1, 1, 3, 1, 1, 2, 6]
def baseStart_2572182 : Nat := 118140960795 + 2572182 * 2 ^ 59
def prefixEnd_2572182 : Nat := 4983230072969 + 3 ^ 40 * 2572182 * 2
def baseEnd_2572182 : Nat := 146751744093684506643973

theorem tailTrace_2572182 : CollatzResearch.WordTrace tailWord_2572182 prefixEnd_2572182 146751744093684506643973 := by
  unfold tailWord_2572182
  simp only [CollatzResearch.WordTrace]
  refine ⟨5863449047964461409796925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 62543456511620921704500533 5863449047964461409796925)
  ·
    refine ⟨2198793392986673028673847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5863449047964461409796925 2198793392986673028673847)
    ·
      refine ⟨3298190089480009543010771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2198793392986673028673847 3298190089480009543010771)
      ·
        refine ⟨4947285134220014314516157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3298190089480009543010771 4947285134220014314516157)
        ·
          refine ⟨1855231925332505367943559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4947285134220014314516157 1855231925332505367943559)
          ·
            refine ⟨2782847887998758051915339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1855231925332505367943559 2782847887998758051915339)
            ·
              refine ⟨4174271831998137077873009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2782847887998758051915339 4174271831998137077873009)
              ·
                refine ⟨3130703873998602808404757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4174271831998137077873009 3130703873998602808404757)
                ·
                  refine ⟨146751744093684506643973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3130703873998602808404757 146751744093684506643973)
                  ·
                    rfl

theorem cell23_2572182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_2572182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572182 prefixEnd_2572182 := by exact prefixLift 2572182
  have htrace : WordTrace (prefixWord ++ tailWord_2572182) baseStart_2572182 baseEnd_2572182 := by
    simpa [prefixWord, tailWord_2572182, baseEnd_2572182] using wordTrace_append hprefix tailTrace_2572182
  have hstable : (prefixWord ++ tailWord_2572182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572182).length < 2 ^ (prefixWord ++ tailWord_2572182).sum := by decide
  have hdescent : baseEnd_2572182 < baseStart_2572182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572191 : List Nat := [1, 1, 2, 5, 3, 1, 1, 1, 4, 4]
def baseStart_2572191 : Nat := 118140960795 + 2572191 * 2 ^ 59
def prefixEnd_2572191 : Nat := 4983230072969 + 3 ^ 40 * 2572191 * 2
def baseEnd_2572191 : Nat := 440256772723017008194405

theorem tailTrace_2572191 : CollatzResearch.WordTrace tailWord_2572191 prefixEnd_2572191 440256772723017008194405 := by
  unfold tailWord_2572191
  simp only [CollatzResearch.WordTrace]
  refine ⟨93815513024398777093828427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62543675349599184729218951 93815513024398777093828427)
  ·
    refine ⟨140723269536598165640742641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93815513024398777093828427 140723269536598165640742641)
    ·
      refine ⟨105542452152448624230556981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140723269536598165640742641 105542452152448624230556981)
      ·
        refine ⟨9894604889292058521614717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105542452152448624230556981 9894604889292058521614717)
        ·
          refine ⟨3710476833484521945605519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9894604889292058521614717 3710476833484521945605519)
          ·
            refine ⟨5565715250226782918408279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3710476833484521945605519 5565715250226782918408279)
            ·
              refine ⟨8348572875340174377612419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5565715250226782918408279 8348572875340174377612419)
              ·
                refine ⟨12522859313010261566418629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8348572875340174377612419 12522859313010261566418629)
                ·
                  refine ⟨2348036121189424043703493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12522859313010261566418629 2348036121189424043703493)
                  ·
                    refine ⟨440256772723017008194405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2348036121189424043703493 440256772723017008194405)
                    ·
                      rfl

theorem cell23_2572191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 4, 4].length) (baseStart_2572191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572191 prefixEnd_2572191 := by exact prefixLift 2572191
  have htrace : WordTrace (prefixWord ++ tailWord_2572191) baseStart_2572191 baseEnd_2572191 := by
    simpa [prefixWord, tailWord_2572191, baseEnd_2572191] using wordTrace_append hprefix tailTrace_2572191
  have hstable : (prefixWord ++ tailWord_2572191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572191).length < 2 ^ (prefixWord ++ tailWord_2572191).sum := by decide
  have hdescent : baseEnd_2572191 < baseStart_2572191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572221 : List Nat := [1, 4, 1, 2, 3, 3, 2, 7]
def baseStart_2572221 : Nat := 118140960795 + 2572221 * 2 ^ 59
def prefixEnd_2572221 : Nat := 4983230072969 + 3 ^ 40 * 2572221 * 2
def baseEnd_2572221 : Nat := 48917989725506885452151

theorem tailTrace_2572221 : CollatzResearch.WordTrace tailWord_2572221 prefixEnd_2572221 48917989725506885452151 := by
  unfold tailWord_2572221
  simp only [CollatzResearch.WordTrace]
  refine ⟨93816607214290092217420517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62544404809526728144947011 93816607214290092217420517)
  ·
    refine ⟨17590613852679392290766347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93816607214290092217420517 17590613852679392290766347)
    ·
      refine ⟨26385920779019088436149521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17590613852679392290766347 26385920779019088436149521)
      ·
        refine ⟨19789440584264316327112141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26385920779019088436149521 19789440584264316327112141)
        ·
          refine ⟨7421040219099118622667053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19789440584264316327112141 7421040219099118622667053)
          ·
            refine ⟨2782890082162169483500145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7421040219099118622667053 2782890082162169483500145)
            ·
              refine ⟨2087167561621627112625109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2782890082162169483500145 2087167561621627112625109)
              ·
                refine ⟨48917989725506885452151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2087167561621627112625109 48917989725506885452151)
                ·
                  rfl

theorem cell23_2572221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 7].length) (baseStart_2572221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572221 prefixEnd_2572221 := by exact prefixLift 2572221
  have htrace : WordTrace (prefixWord ++ tailWord_2572221) baseStart_2572221 baseEnd_2572221 := by
    simpa [prefixWord, tailWord_2572221, baseEnd_2572221] using wordTrace_append hprefix tailTrace_2572221
  have hstable : (prefixWord ++ tailWord_2572221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572221).length < 2 ^ (prefixWord ++ tailWord_2572221).sum := by decide
  have hdescent : baseEnd_2572221 < baseStart_2572221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572232 : List Nat := [2, 1, 3, 1, 4, 3, 1, 3, 1, 2, 2]
def baseStart_2572232 : Nat := 118140960795 + 2572232 * 2 ^ 59
def prefixEnd_2572232 : Nat := 4983230072969 + 3 ^ 40 * 2572232 * 2
def baseEnd_2572232 : Nat := 1320791370875885364170527

theorem tailTrace_2572232 : CollatzResearch.WordTrace tailWord_2572232 prefixEnd_2572232 1320791370875885364170527 := by
  unfold tailWord_2572232
  simp only [CollatzResearch.WordTrace]
  refine ⟨46908504208625120548035475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62544672278166827397380633 46908504208625120548035475)
  ·
    refine ⟨70362756312937680822053213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46908504208625120548035475 70362756312937680822053213)
    ·
      refine ⟨26386033617351630308269955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70362756312937680822053213 26386033617351630308269955)
      ·
        refine ⟨39579050426027445462404933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26386033617351630308269955 39579050426027445462404933)
        ·
          refine ⟨7421071954880146024200925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39579050426027445462404933 7421071954880146024200925)
          ·
            refine ⟨2782901983080054759075347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7421071954880146024200925 2782901983080054759075347)
            ·
              refine ⟨4174352974620082138613021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2782901983080054759075347 4174352974620082138613021)
              ·
                refine ⟨1565382365482530801979883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4174352974620082138613021 1565382365482530801979883)
                ·
                  refine ⟨2348073548223796202969825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1565382365482530801979883 2348073548223796202969825)
                  ·
                    refine ⟨1761055161167847152227369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2348073548223796202969825 1761055161167847152227369)
                    ·
                      refine ⟨1320791370875885364170527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1761055161167847152227369 1320791370875885364170527)
                      ·
                        rfl

theorem cell23_2572232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 3, 1, 2, 2].length) (baseStart_2572232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572232 prefixEnd_2572232 := by exact prefixLift 2572232
  have htrace : WordTrace (prefixWord ++ tailWord_2572232) baseStart_2572232 baseEnd_2572232 := by
    simpa [prefixWord, tailWord_2572232, baseEnd_2572232] using wordTrace_append hprefix tailTrace_2572232
  have hstable : (prefixWord ++ tailWord_2572232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572232).length < 2 ^ (prefixWord ++ tailWord_2572232).sum := by decide
  have hdescent : baseEnd_2572232 < baseStart_2572232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572244 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 2, 2, 5]
def baseStart_2572244 : Nat := 118140960795 + 2572244 * 2 ^ 59
def prefixEnd_2572244 : Nat := 4983230072969 + 3 ^ 40 * 2572244 * 2
def baseEnd_2572244 : Nat := 1320797532643739317220471

theorem tailTrace_2572244 : CollatzResearch.WordTrace tailWord_2572244 prefixEnd_2572244 1320797532643739317220471 := by
  unfold tailWord_2572244
  simp only [CollatzResearch.WordTrace]
  refine ⟨46908723046603383572753893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62544964062137844763671857 46908723046603383572753893)
  ·
    refine ⟨8795385571238134419891355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46908723046603383572753893 8795385571238134419891355)
    ·
      refine ⟨13193078356857201629837033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8795385571238134419891355 13193078356857201629837033)
      ·
        refine ⟨9894808767642901222377775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13193078356857201629837033 9894808767642901222377775)
        ·
          refine ⟨14842213151464351833566663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9894808767642901222377775 14842213151464351833566663)
          ·
            refine ⟨22263319727196527750349995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14842213151464351833566663 22263319727196527750349995)
            ·
              refine ⟨33394979590794791625524993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22263319727196527750349995 33394979590794791625524993)
              ·
                refine ⟨25046234693096093719143745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33394979590794791625524993 25046234693096093719143745)
                ·
                  refine ⟨18784676019822070289357809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25046234693096093719143745 18784676019822070289357809)
                  ·
                    refine ⟨14088507014866552717018357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18784676019822070289357809 14088507014866552717018357)
                    ·
                      refine ⟨1320797532643739317220471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14088507014866552717018357 1320797532643739317220471)
                      ·
                        rfl

theorem cell23_2572244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_2572244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572244 prefixEnd_2572244 := by exact prefixLift 2572244
  have htrace : WordTrace (prefixWord ++ tailWord_2572244) baseStart_2572244 baseEnd_2572244 := by
    simpa [prefixWord, tailWord_2572244, baseEnd_2572244] using wordTrace_append hprefix tailTrace_2572244
  have hstable : (prefixWord ++ tailWord_2572244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572244).length < 2 ^ (prefixWord ++ tailWord_2572244).sum := by decide
  have hdescent : baseEnd_2572244 < baseStart_2572244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572267 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 6]
def baseStart_2572267 : Nat := 118140960795 + 2572267 * 2 ^ 59
def prefixEnd_2572267 : Nat := 4983230072969 + 3 ^ 40 * 2572267 * 2
def baseEnd_2572267 : Nat := 1320809342698792727232865

theorem tailTrace_2572267 : CollatzResearch.WordTrace tailWord_2572267 prefixEnd_2572267 1320809342698792727232865 := by
  unfold tailWord_2572267
  simp only [CollatzResearch.WordTrace]
  refine ⟨93818284972123442073595055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62545523314748961382396703 93818284972123442073595055)
  ·
    refine ⟨140727427458185163110392583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93818284972123442073595055 140727427458185163110392583)
    ·
      refine ⟨211091141187277744665588875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140727427458185163110392583 211091141187277744665588875)
      ·
        refine ⟨316636711780916616998383313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211091141187277744665588875 316636711780916616998383313)
        ·
          refine ⟨237477533835687462748787485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 316636711780916616998383313 237477533835687462748787485)
          ·
            refine ⟨89054075188382798530795307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 237477533835687462748787485 89054075188382798530795307)
            ·
              refine ⟨133581112782574197796192961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89054075188382798530795307 133581112782574197796192961)
              ·
                refine ⟨100185834586930648347144721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133581112782574197796192961 100185834586930648347144721)
                ·
                  refine ⟨75139375940197986260358541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100185834586930648347144721 75139375940197986260358541)
                  ·
                    refine ⟨28177265977574244847634453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75139375940197986260358541 28177265977574244847634453)
                    ·
                      refine ⟨1320809342698792727232865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28177265977574244847634453 1320809342698792727232865)
                      ·
                        rfl

theorem cell23_2572267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 6].length) (baseStart_2572267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572267 prefixEnd_2572267 := by exact prefixLift 2572267
  have htrace : WordTrace (prefixWord ++ tailWord_2572267) baseStart_2572267 baseEnd_2572267 := by
    simpa [prefixWord, tailWord_2572267, baseEnd_2572267] using wordTrace_append hprefix tailTrace_2572267
  have hstable : (prefixWord ++ tailWord_2572267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572267).length < 2 ^ (prefixWord ++ tailWord_2572267).sum := by decide
  have hdescent : baseEnd_2572267 < baseStart_2572267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572271 : List Nat := [1, 1, 2, 1, 4, 2, 2, 3, 1, 4, 2]
def baseStart_2572271 : Nat := 118140960795 + 2572271 * 2 ^ 59
def prefixEnd_2572271 : Nat := 4983230072969 + 3 ^ 40 * 2572271 * 2
def baseEnd_2572271 : Nat := 1320811396621410711582847

theorem tailTrace_2572271 : CollatzResearch.WordTrace tailWord_2572271 prefixEnd_2572271 1320811396621410711582847 := by
  unfold tailWord_2572271
  simp only [CollatzResearch.WordTrace]
  refine ⟨93818430864108950756740667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62545620576072633837827111 93818430864108950756740667)
  ·
    refine ⟨140727646296163426135111001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93818430864108950756740667 140727646296163426135111001)
    ·
      refine ⟨105545734722122569601333251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140727646296163426135111001 105545734722122569601333251)
      ·
        refine ⟨158318602083183854401999877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105545734722122569601333251 158318602083183854401999877)
        ·
          refine ⟨29684737890596972700374977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158318602083183854401999877 29684737890596972700374977)
          ·
            refine ⟨22263553417947729525281233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29684737890596972700374977 22263553417947729525281233)
            ·
              refine ⟨16697665063460797143960925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22263553417947729525281233 16697665063460797143960925)
              ·
                refine ⟨6261624398797798928985347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16697665063460797143960925 6261624398797798928985347)
                ·
                  refine ⟨9392436598196698393478021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6261624398797798928985347 9392436598196698393478021)
                  ·
                    refine ⟨1761081862161880948777129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9392436598196698393478021 1761081862161880948777129)
                    ·
                      refine ⟨1320811396621410711582847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1761081862161880948777129 1320811396621410711582847)
                      ·
                        rfl

theorem cell23_2572271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 4, 2].length) (baseStart_2572271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572271 prefixEnd_2572271 := by exact prefixLift 2572271
  have htrace : WordTrace (prefixWord ++ tailWord_2572271) baseStart_2572271 baseEnd_2572271 := by
    simpa [prefixWord, tailWord_2572271, baseEnd_2572271] using wordTrace_append hprefix tailTrace_2572271
  have hstable : (prefixWord ++ tailWord_2572271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572271).length < 2 ^ (prefixWord ++ tailWord_2572271).sum := by decide
  have hdescent : baseEnd_2572271 < baseStart_2572271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572304 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 3]
def baseStart_2572304 : Nat := 118140960795 + 2572304 * 2 ^ 59
def prefixEnd_2572304 : Nat := 4983230072969 + 3 ^ 40 * 2572304 * 2
def baseEnd_2572304 : Nat := 1320828341483009082470195

theorem tailTrace_2572304 : CollatzResearch.WordTrace tailWord_2572304 prefixEnd_2572304 1320828341483009082470195 := by
  unfold tailWord_2572304
  simp only [CollatzResearch.WordTrace]
  refine ⟨46909817236494698696345983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62546422981992931595127977 46909817236494698696345983)
  ·
    refine ⟨70364725854742048044518975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46909817236494698696345983 70364725854742048044518975)
    ·
      refine ⟨105547088782113072066778463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70364725854742048044518975 105547088782113072066778463)
      ·
        refine ⟨158320633173169608100167695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105547088782113072066778463 158320633173169608100167695)
        ·
          refine ⟨237480949759754412150251543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158320633173169608100167695 237480949759754412150251543)
          ·
            refine ⟨356221424639631618225377315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237480949759754412150251543 356221424639631618225377315)
            ·
              refine ⟨534332136959447427338065973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356221424639631618225377315 534332136959447427338065973)
              ·
                refine ⟨50093637839948196312943685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 534332136959447427338065973 50093637839948196312943685)
                ·
                  refine ⟨9392557094990286808676941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50093637839948196312943685 9392557094990286808676941)
                  ·
                    refine ⟨3522208910621357553253853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9392557094990286808676941 3522208910621357553253853)
                    ·
                      refine ⟨1320828341483009082470195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3522208910621357553253853 1320828341483009082470195)
                      ·
                        rfl

theorem cell23_2572304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 3].length) (baseStart_2572304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572304 prefixEnd_2572304 := by exact prefixLift 2572304
  have htrace : WordTrace (prefixWord ++ tailWord_2572304) baseStart_2572304 baseEnd_2572304 := by
    simpa [prefixWord, tailWord_2572304, baseEnd_2572304] using wordTrace_append hprefix tailTrace_2572304
  have hstable : (prefixWord ++ tailWord_2572304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572304).length < 2 ^ (prefixWord ++ tailWord_2572304).sum := by decide
  have hdescent : baseEnd_2572304 < baseStart_2572304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572328 : List Nat := [2, 1, 5, 3, 1, 1, 1, 2, 7]
def baseStart_2572328 : Nat := 118140960795 + 2572328 * 2 ^ 59
def prefixEnd_2572328 : Nat := 4983230072969 + 3 ^ 40 * 2572328 * 2
def baseEnd_2572328 : Nat := 146760073890968554285565

theorem tailTrace_2572328 : CollatzResearch.WordTrace tailWord_2572328 prefixEnd_2572328 146760073890968554285565 := by
  unfold tailWord_2572328
  simp only [CollatzResearch.WordTrace]
  refine ⟨46910254912451224745782819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 62547006549934966327710425 46910254912451224745782819)
  ·
    refine ⟨70365382368676837118674229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46910254912451224745782819 70365382368676837118674229)
    ·
      refine ⟨6596754597063453479875709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70365382368676837118674229 6596754597063453479875709)
      ·
        refine ⟨2473782973898795054953391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6596754597063453479875709 2473782973898795054953391)
        ·
          refine ⟨3710674460848192582430087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2473782973898795054953391 3710674460848192582430087)
          ·
            refine ⟨5566011691272288873645131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3710674460848192582430087 5566011691272288873645131)
            ·
              refine ⟨8349017536908433310467697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5566011691272288873645131 8349017536908433310467697)
              ·
                refine ⟨6261763152681324982850773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8349017536908433310467697 6261763152681324982850773)
                ·
                  refine ⟨146760073890968554285565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6261763152681324982850773 146760073890968554285565)
                  ·
                    rfl

theorem cell23_2572328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 7].length) (baseStart_2572328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572328 prefixEnd_2572328 := by exact prefixLift 2572328
  have htrace : WordTrace (prefixWord ++ tailWord_2572328) baseStart_2572328 baseEnd_2572328 := by
    simpa [prefixWord, tailWord_2572328, baseEnd_2572328] using wordTrace_append hprefix tailTrace_2572328
  have hstable : (prefixWord ++ tailWord_2572328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572328).length < 2 ^ (prefixWord ++ tailWord_2572328).sum := by decide
  have hdescent : baseEnd_2572328 < baseStart_2572328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572341 : List Nat := [1, 3, 3, 1, 1, 1, 5, 1, 2, 5]
def baseStart_2572341 : Nat := 118140960795 + 2572341 * 2 ^ 59
def prefixEnd_2572341 : Nat := 4983230072969 + 3 ^ 40 * 2572341 * 2
def baseEnd_2572341 : Nat := 440282446755741812569175

theorem tailTrace_2572341 : CollatzResearch.WordTrace tailWord_2572341 prefixEnd_2572341 440282446755741812569175 := by
  unfold tailWord_2572341
  simp only [CollatzResearch.WordTrace]
  refine ⟨93820983973855352711788877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62547322649236901807859251 93820983973855352711788877)
  ·
    refine ⟨35182868990195757266920829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93820983973855352711788877 35182868990195757266920829)
    ·
      refine ⟨13193575871323408975095311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35182868990195757266920829 13193575871323408975095311)
      ·
        refine ⟨19790363806985113462642967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13193575871323408975095311 19790363806985113462642967)
        ·
          refine ⟨29685545710477670193964451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19790363806985113462642967 29685545710477670193964451)
          ·
            refine ⟨44528318565716505290946677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29685545710477670193964451 44528318565716505290946677)
            ·
              refine ⟨4174529865535922371026251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44528318565716505290946677 4174529865535922371026251)
              ·
                refine ⟨6261794798303883556539377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4174529865535922371026251 6261794798303883556539377)
                ·
                  refine ⟨4696346098727912667404533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6261794798303883556539377 4696346098727912667404533)
                  ·
                    refine ⟨440282446755741812569175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4696346098727912667404533 440282446755741812569175)
                    ·
                      rfl

theorem cell23_2572341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_2572341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572341 prefixEnd_2572341 := by exact prefixLift 2572341
  have htrace : WordTrace (prefixWord ++ tailWord_2572341) baseStart_2572341 baseEnd_2572341 := by
    simpa [prefixWord, tailWord_2572341, baseEnd_2572341] using wordTrace_append hprefix tailTrace_2572341
  have hstable : (prefixWord ++ tailWord_2572341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572341).length < 2 ^ (prefixWord ++ tailWord_2572341).sum := by decide
  have hdescent : baseEnd_2572341 < baseStart_2572341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572358 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 4, 5]
def baseStart_2572358 : Nat := 118140960795 + 2572358 * 2 ^ 59
def prefixEnd_2572358 : Nat := 4983230072969 + 3 ^ 40 * 2572358 * 2
def baseEnd_2572358 : Nat := 440285356479450623731649

theorem tailTrace_2572358 : CollatzResearch.WordTrace tailWord_2572358 prefixEnd_2572358 440285356479450623731649 := by
  unfold tailWord_2572358
  simp only [CollatzResearch.WordTrace]
  refine ⟨2931925125462305144223679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 62547736009862509743438485 2931925125462305144223679)
  ·
    refine ⟨4397887688193457716335519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2931925125462305144223679 4397887688193457716335519)
    ·
      refine ⟨6596831532290186574503279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4397887688193457716335519 6596831532290186574503279)
      ·
        refine ⟨9895247298435279861754919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6596831532290186574503279 9895247298435279861754919)
        ·
          refine ⟨14842870947652919792632379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9895247298435279861754919 14842870947652919792632379)
          ·
            refine ⟨22264306421479379688948569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14842870947652919792632379 22264306421479379688948569)
            ·
              refine ⟨16698229816109534766711427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22264306421479379688948569 16698229816109534766711427)
              ·
                refine ⟨25047344724164302150067141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16698229816109534766711427 25047344724164302150067141)
                ·
                  refine ⟨4696377135780806653137589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25047344724164302150067141 4696377135780806653137589)
                  ·
                    refine ⟨440285356479450623731649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4696377135780806653137589 440285356479450623731649)
                    ·
                      rfl

theorem cell23_2572358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_2572358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572358 prefixEnd_2572358 := by exact prefixLift 2572358
  have htrace : WordTrace (prefixWord ++ tailWord_2572358) baseStart_2572358 baseEnd_2572358 := by
    simpa [prefixWord, tailWord_2572358, baseEnd_2572358] using wordTrace_append hprefix tailTrace_2572358
  have hstable : (prefixWord ++ tailWord_2572358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572358).length < 2 ^ (prefixWord ++ tailWord_2572358).sum := by decide
  have hdescent : baseEnd_2572358 < baseStart_2572358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2572361 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 4, 4, 2]
def baseStart_2572361 : Nat := 118140960795 + 2572361 * 2 ^ 59
def prefixEnd_2572361 : Nat := 4983230072969 + 3 ^ 40 * 2572361 * 2
def baseEnd_2572361 : Nat := 1320857609880315359457433

theorem tailTrace_2572361 : CollatzResearch.WordTrace tailWord_2572361 prefixEnd_2572361 1320857609880315359457433 := by
  unfold tailWord_2572361
  simp only [CollatzResearch.WordTrace]
  refine ⟨93821713433782896127516937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 62547808955855264085011291 93821713433782896127516937)
  ·
    refine ⟨70366285075337172095637703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93821713433782896127516937 70366285075337172095637703)
    ·
      refine ⟨105549427613005758143456555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70366285075337172095637703 105549427613005758143456555)
      ·
        refine ⟨158324141419508637215184833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105549427613005758143456555 158324141419508637215184833)
        ·
          refine ⟨118743106064631477911388625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158324141419508637215184833 118743106064631477911388625)
          ·
            refine ⟨89057329548473608433541469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118743106064631477911388625 89057329548473608433541469)
            ·
              refine ⟨33396498580677603162578051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89057329548473608433541469 33396498580677603162578051)
              ·
                refine ⟨50094747871016404743867077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33396498580677603162578051 50094747871016404743867077)
                ·
                  refine ⟨9392765225815575889475077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50094747871016404743867077 9392765225815575889475077)
                  ·
                    refine ⟨1761143479840420479276577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9392765225815575889475077 1761143479840420479276577)
                    ·
                      refine ⟨1320857609880315359457433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1761143479840420479276577 1320857609880315359457433)
                      ·
                        rfl

theorem cell23_2572361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 4, 2].length) (baseStart_2572361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2572361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2572361 prefixEnd_2572361 := by exact prefixLift 2572361
  have htrace : WordTrace (prefixWord ++ tailWord_2572361) baseStart_2572361 baseEnd_2572361 := by
    simpa [prefixWord, tailWord_2572361, baseEnd_2572361] using wordTrace_append hprefix tailTrace_2572361
  have hstable : (prefixWord ++ tailWord_2572361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2572361).length < 2 ^ (prefixWord ++ tailWord_2572361).sum := by decide
  have hdescent : baseEnd_2572361 < baseStart_2572361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2572361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
