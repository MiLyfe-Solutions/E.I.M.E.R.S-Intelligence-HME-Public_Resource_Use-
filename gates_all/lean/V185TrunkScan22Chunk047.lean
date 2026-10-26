import V185TrunkScan22Chunk046

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_420867 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 2, 9]
def baseStart_420867 : Nat := 118140960795 + 420867 * 2 ^ 59
def prefixEnd_420867 : Nat := 4983230072969 + 3 ^ 40 * 420867 * 2
def baseEnd_420867 : Nat := 144071375077273393084649

theorem tailTrace_420867 : CollatzResearch.WordTrace tailWord_420867 prefixEnd_420867 144071375077273393084649 := by
  unfold tailWord_420867
  simp only [CollatzResearch.WordTrace]
  refine ⟨15350280566278212206180855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10233520377518808137453903 15350280566278212206180855)
  ·
    refine ⟨23025420849417318309271283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15350280566278212206180855 23025420849417318309271283)
    ·
      refine ⟨34538131274125977463906925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23025420849417318309271283 34538131274125977463906925)
      ·
        refine ⟨12951799227797241548965097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34538131274125977463906925 12951799227797241548965097)
        ·
          refine ⟨9713849420847931161723823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12951799227797241548965097 9713849420847931161723823)
          ·
            refine ⟨14570774131271896742585735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9713849420847931161723823 14570774131271896742585735)
            ·
              refine ⟨21856161196907845113878603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14570774131271896742585735 21856161196907845113878603)
              ·
                refine ⟨32784241795361767670817905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21856161196907845113878603 32784241795361767670817905)
                ·
                  refine ⟨24588181346521325753113429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32784241795361767670817905 24588181346521325753113429)
                  ·
                    refine ⟨144071375077273393084649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 24588181346521325753113429 144071375077273393084649)
                    ·
                      rfl

theorem cell22_420867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 9].length) (baseStart_420867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_420867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_420867 prefixEnd_420867 := by exact prefixLift 420867
  have htrace : WordTrace (prefixWord ++ tailWord_420867) baseStart_420867 baseEnd_420867 := by
    simpa [prefixWord, tailWord_420867, baseEnd_420867] using wordTrace_append hprefix tailTrace_420867
  have hstable : (prefixWord ++ tailWord_420867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420867).length < 2 ^ (prefixWord ++ tailWord_420867).sum := by decide
  have hdescent : baseEnd_420867 < baseStart_420867 := by decide
  rcases family_descends (prefixWord ++ tailWord_420867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420869 : List Nat := [1, 3, 1, 1, 2, 3, 4, 1, 6]
def baseStart_420869 : Nat := 118140960795 + 420869 * 2 ^ 59
def prefixEnd_420869 : Nat := 4983230072969 + 3 ^ 40 * 420869 * 2
def baseEnd_420869 : Nat := 48024019906048684844881

theorem tailTrace_420869 : CollatzResearch.WordTrace tailWord_420869 prefixEnd_420869 48024019906048684844881 := by
  unfold tailWord_420869
  simp only [CollatzResearch.WordTrace]
  refine ⟨15350353512270966547753661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10233569008180644365169107 15350353512270966547753661)
  ·
    refine ⟨5756382567101612455407623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15350353512270966547753661 5756382567101612455407623)
    ·
      refine ⟨8634573850652418683111435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5756382567101612455407623 8634573850652418683111435)
      ·
        refine ⟨12951860775978628024667153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8634573850652418683111435 12951860775978628024667153)
        ·
          refine ⟨9713895581983971018500365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12951860775978628024667153 9713895581983971018500365)
          ·
            refine ⟨3642710843243989131937637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9713895581983971018500365 3642710843243989131937637)
            ·
              refine ⟨683008283108247962238307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3642710843243989131937637 683008283108247962238307)
              ·
                refine ⟨1024512424662371943357461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 683008283108247962238307 1024512424662371943357461)
                ·
                  refine ⟨48024019906048684844881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1024512424662371943357461 48024019906048684844881)
                  ·
                    rfl

theorem cell22_420869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 6].length) (baseStart_420869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_420869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_420869 prefixEnd_420869 := by exact prefixLift 420869
  have htrace : WordTrace (prefixWord ++ tailWord_420869) baseStart_420869 baseEnd_420869 := by
    simpa [prefixWord, tailWord_420869, baseEnd_420869] using wordTrace_append hprefix tailTrace_420869
  have hstable : (prefixWord ++ tailWord_420869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420869).length < 2 ^ (prefixWord ++ tailWord_420869).sum := by decide
  have hdescent : baseEnd_420869 < baseStart_420869 := by decide
  rcases family_descends (prefixWord ++ tailWord_420869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420899 : List Nat := [1, 1, 1, 4, 3, 2, 2, 1, 1, 6]
def baseStart_420899 : Nat := 118140960795 + 420899 * 2 ^ 59
def prefixEnd_420899 : Nat := 4983230072969 + 3 ^ 40 * 420899 * 2
def baseEnd_420899 : Nat := 144082329331235976284551

theorem tailTrace_420899 : CollatzResearch.WordTrace tailWord_420899 prefixEnd_420899 144082329331235976284551 := by
  unfold tailWord_420899
  simp only [CollatzResearch.WordTrace]
  refine ⟨15351447702162281671345751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10234298468108187780897167 15351447702162281671345751)
  ·
    refine ⟨23027171553243422507018627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15351447702162281671345751 23027171553243422507018627)
    ·
      refine ⟨34540757329865133760527941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23027171553243422507018627 34540757329865133760527941)
      ·
        refine ⟨6476391999349712580098989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34540757329865133760527941 6476391999349712580098989)
        ·
          refine ⟨2428646999756142217537121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6476391999349712580098989 2428646999756142217537121)
          ·
            refine ⟨1821485249817106663152841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2428646999756142217537121 1821485249817106663152841)
            ·
              refine ⟨1366113937362829997364631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1821485249817106663152841 1366113937362829997364631)
              ·
                refine ⟨2049170906044244996046947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1366113937362829997364631 2049170906044244996046947)
                ·
                  refine ⟨3073756359066367494070421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2049170906044244996046947 3073756359066367494070421)
                  ·
                    refine ⟨144082329331235976284551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3073756359066367494070421 144082329331235976284551)
                    ·
                      rfl

theorem cell22_420899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 6].length) (baseStart_420899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_420899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_420899 prefixEnd_420899 := by exact prefixLift 420899
  have htrace : WordTrace (prefixWord ++ tailWord_420899) baseStart_420899 baseEnd_420899 := by
    simpa [prefixWord, tailWord_420899, baseEnd_420899] using wordTrace_append hprefix tailTrace_420899
  have hstable : (prefixWord ++ tailWord_420899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420899).length < 2 ^ (prefixWord ++ tailWord_420899).sum := by decide
  have hdescent : baseEnd_420899 < baseStart_420899 := by decide
  rcases family_descends (prefixWord ++ tailWord_420899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420918 : List Nat := [5, 1, 2, 1, 1, 2, 2, 1, 4, 3]
def baseStart_420918 : Nat := 118140960795 + 420918 * 2 ^ 59
def prefixEnd_420918 : Nat := 4983230072969 + 3 ^ 40 * 420918 * 2
def baseEnd_420918 : Nat := 144088833419526260059493

theorem tailTrace_420918 : CollatzResearch.WordTrace tailWord_420918 prefixEnd_420918 144088833419526260059493 := by
  unfold tailWord_420918
  simp only [CollatzResearch.WordTrace]
  refine ⟨959508793068340494767963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10234760459395631944191605 959508793068340494767963)
  ·
    refine ⟨1439263189602510742151945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 959508793068340494767963 1439263189602510742151945)
    ·
      refine ⟨1079447392201883056613959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1439263189602510742151945 1079447392201883056613959)
      ·
        refine ⟨1619171088302824584920939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1079447392201883056613959 1619171088302824584920939)
        ·
          refine ⟨2428756632454236877381409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1619171088302824584920939 2428756632454236877381409)
          ·
            refine ⟨1821567474340677658036057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2428756632454236877381409 1821567474340677658036057)
            ·
              refine ⟨1366175605755508243527043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1821567474340677658036057 1366175605755508243527043)
              ·
                refine ⟨2049263408633262365290565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1366175605755508243527043 2049263408633262365290565)
                ·
                  refine ⟨384236889118736693491981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2049263408633262365290565 384236889118736693491981)
                  ·
                    refine ⟨144088833419526260059493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 384236889118736693491981 144088833419526260059493)
                    ·
                      rfl

theorem cell22_420918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_420918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_420918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_420918 prefixEnd_420918 := by exact prefixLift 420918
  have htrace : WordTrace (prefixWord ++ tailWord_420918) baseStart_420918 baseEnd_420918 := by
    simpa [prefixWord, tailWord_420918, baseEnd_420918] using wordTrace_append hprefix tailTrace_420918
  have hstable : (prefixWord ++ tailWord_420918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420918).length < 2 ^ (prefixWord ++ tailWord_420918).sum := by decide
  have hdescent : baseEnd_420918 < baseStart_420918 := by decide
  rcases family_descends (prefixWord ++ tailWord_420918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420935 : List Nat := [1, 1, 4, 1, 3, 4, 2, 1, 2, 3]
def baseStart_420935 : Nat := 118140960795 + 420935 * 2 ^ 59
def prefixEnd_420935 : Nat := 4983230072969 + 3 ^ 40 * 420935 * 2
def baseEnd_420935 : Nat := 144094652866943882384441

theorem tailTrace_420935 : CollatzResearch.WordTrace tailWord_420935 prefixEnd_420935 144094652866943882384441 := by
  unfold tailWord_420935
  simp only [CollatzResearch.WordTrace]
  refine ⟨15352760730031859819656259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10235173820021239879770839 15352760730031859819656259)
  ·
    refine ⟨23029141095047789729484389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15352760730031859819656259 23029141095047789729484389)
    ·
      refine ⟨4317963955321460574278323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23029141095047789729484389 4317963955321460574278323)
      ·
        refine ⟨6476945932982190861417485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4317963955321460574278323 6476945932982190861417485)
        ·
          refine ⟨2428854724868321573031557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6476945932982190861417485 2428854724868321573031557)
          ·
            refine ⟨455410260912810294943417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2428854724868321573031557 455410260912810294943417)
            ·
              refine ⟨341557695684607721207563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 455410260912810294943417 341557695684607721207563)
              ·
                refine ⟨512336543526911581811345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 341557695684607721207563 512336543526911581811345)
                ·
                  refine ⟨384252407645183686358509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 512336543526911581811345 384252407645183686358509)
                  ·
                    refine ⟨144094652866943882384441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 384252407645183686358509 144094652866943882384441)
                    ·
                      rfl

theorem cell22_420935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_420935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_420935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_420935 prefixEnd_420935 := by exact prefixLift 420935
  have htrace : WordTrace (prefixWord ++ tailWord_420935) baseStart_420935 baseEnd_420935 := by
    simpa [prefixWord, tailWord_420935, baseEnd_420935] using wordTrace_append hprefix tailTrace_420935
  have hstable : (prefixWord ++ tailWord_420935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420935).length < 2 ^ (prefixWord ++ tailWord_420935).sum := by decide
  have hdescent : baseEnd_420935 < baseStart_420935 := by decide
  rcases family_descends (prefixWord ++ tailWord_420935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420963 : List Nat := [1, 1, 1, 5, 1, 1, 1, 7, 1, 3]
def baseStart_420963 : Nat := 118140960795 + 420963 * 2 ^ 59
def prefixEnd_420963 : Nat := 4983230072969 + 3 ^ 40 * 420963 * 2
def baseEnd_420963 : Nat := 144104237839161142684355

theorem tailTrace_420963 : CollatzResearch.WordTrace tailWord_420963 prefixEnd_420963 144104237839161142684355 := by
  unfold tailWord_420963
  simp only [CollatzResearch.WordTrace]
  refine ⟨15353781973930420601675543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10235854649286947067783695 15353781973930420601675543)
  ·
    refine ⟨23030672960895630902513315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15353781973930420601675543 23030672960895630902513315)
    ·
      refine ⟨34546009441343446353769973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23030672960895630902513315 34546009441343446353769973)
      ·
        refine ⟨3238688385125948095665935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34546009441343446353769973 3238688385125948095665935)
        ·
          refine ⟨4858032577688922143498903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3238688385125948095665935 4858032577688922143498903)
          ·
            refine ⟨7287048866533383215248355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4858032577688922143498903 7287048866533383215248355)
            ·
              refine ⟨10930573299800074822872533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7287048866533383215248355 10930573299800074822872533)
              ·
                refine ⟨256185311714064253661075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 10930573299800074822872533 256185311714064253661075)
                ·
                  refine ⟨384277967571096380491613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 256185311714064253661075 384277967571096380491613)
                  ·
                    refine ⟨144104237839161142684355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 384277967571096380491613 144104237839161142684355)
                    ·
                      rfl

theorem cell22_420963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 7, 1, 3].length) (baseStart_420963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_420963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_420963 prefixEnd_420963 := by exact prefixLift 420963
  have htrace : WordTrace (prefixWord ++ tailWord_420963) baseStart_420963 baseEnd_420963 := by
    simpa [prefixWord, tailWord_420963, baseEnd_420963] using wordTrace_append hprefix tailTrace_420963
  have hstable : (prefixWord ++ tailWord_420963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420963).length < 2 ^ (prefixWord ++ tailWord_420963).sum := by decide
  have hdescent : baseEnd_420963 < baseStart_420963 := by decide
  rcases family_descends (prefixWord ++ tailWord_420963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420976 : List Nat := [2, 1, 1, 1, 5, 1, 4, 2, 5]
def baseStart_420976 : Nat := 118140960795 + 420976 * 2 ^ 59
def prefixEnd_420976 : Nat := 4983230072969 + 3 ^ 40 * 420976 * 2
def baseEnd_420976 : Nat := 48036229334944480703105

theorem tailTrace_420976 : CollatzResearch.WordTrace tailWord_420976 prefixEnd_420976 48036229334944480703105 := by
  unfold tailWord_420976
  simp only [CollatzResearch.WordTrace]
  refine ⟨7677128061441661910949391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10236170748588882547932521 7677128061441661910949391)
  ·
    refine ⟨11515692092162492866424087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7677128061441661910949391 11515692092162492866424087)
    ·
      refine ⟨17273538138243739299636131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11515692092162492866424087 17273538138243739299636131)
      ·
        refine ⟨25910307207365608949454197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17273538138243739299636131 25910307207365608949454197)
        ·
          refine ⟨2429091300690525839011331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25910307207365608949454197 2429091300690525839011331)
          ·
            refine ⟨3643636951035788758516997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2429091300690525839011331 3643636951035788758516997)
            ·
              refine ⟨683181928319210392221937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3643636951035788758516997 683181928319210392221937)
              ·
                refine ⟨512386446239407794166453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 683181928319210392221937 512386446239407794166453)
                ·
                  refine ⟨48036229334944480703105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 512386446239407794166453 48036229334944480703105)
                  ·
                    rfl

theorem cell22_420976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 5].length) (baseStart_420976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_420976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_420976 prefixEnd_420976 := by exact prefixLift 420976
  have htrace : WordTrace (prefixWord ++ tailWord_420976) baseStart_420976 baseEnd_420976 := by
    simpa [prefixWord, tailWord_420976, baseEnd_420976] using wordTrace_append hprefix tailTrace_420976
  have hstable : (prefixWord ++ tailWord_420976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420976).length < 2 ^ (prefixWord ++ tailWord_420976).sum := by decide
  have hdescent : baseEnd_420976 < baseStart_420976 := by decide
  rcases family_descends (prefixWord ++ tailWord_420976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421053 : List Nat := [1, 4, 1, 2, 1, 1, 2, 5, 2, 3]
def baseStart_421053 : Nat := 118140960795 + 421053 * 2 ^ 59
def prefixEnd_421053 : Nat := 4983230072969 + 3 ^ 40 * 421053 * 2
def baseEnd_421053 : Nat := 144135046678430907934079

theorem tailTrace_421053 : CollatzResearch.WordTrace tailWord_421053 prefixEnd_421053 144135046678430907934079 := by
  unfold tailWord_421053
  simp only [CollatzResearch.WordTrace]
  refine ⟨15357064543604365972451813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10238043029069577314967875 15357064543604365972451813)
  ·
    refine ⟨2879449601925818619834715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15357064543604365972451813 2879449601925818619834715)
    ·
      refine ⟨4319174402888727929752073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2879449601925818619834715 4319174402888727929752073)
      ·
        refine ⟨3239380802166545947314055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4319174402888727929752073 3239380802166545947314055)
        ·
          refine ⟨4859071203249818920971083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3239380802166545947314055 4859071203249818920971083)
          ·
            refine ⟨7288606804874728381456625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4859071203249818920971083 7288606804874728381456625)
            ·
              refine ⟨5466455103656046286092469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7288606804874728381456625 5466455103656046286092469)
              ·
                refine ⟨512480165967754339321169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5466455103656046286092469 512480165967754339321169)
                ·
                  refine ⟨384360124475815754490877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 512480165967754339321169 384360124475815754490877)
                  ·
                    refine ⟨144135046678430907934079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 384360124475815754490877 144135046678430907934079)
                    ·
                      rfl

theorem cell22_421053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_421053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_421053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_421053 prefixEnd_421053 := by exact prefixLift 421053
  have htrace : WordTrace (prefixWord ++ tailWord_421053) baseStart_421053 baseEnd_421053 := by
    simpa [prefixWord, tailWord_421053, baseEnd_421053] using wordTrace_append hprefix tailTrace_421053
  have hstable : (prefixWord ++ tailWord_421053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421053).length < 2 ^ (prefixWord ++ tailWord_421053).sum := by decide
  have hdescent : baseEnd_421053 < baseStart_421053 := by decide
  rcases family_descends (prefixWord ++ tailWord_421053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421066 : List Nat := [3, 1, 2, 1, 3, 3, 1, 8]
def baseStart_421066 : Nat := 118140960795 + 421066 * 2 ^ 59
def prefixEnd_421066 : Nat := 4983230072969 + 3 ^ 40 * 421066 * 2
def baseEnd_421066 : Nat := 16015499649344800817671

theorem tailTrace_421066 : CollatzResearch.WordTrace tailWord_421066 prefixEnd_421066 16015499649344800817671 := by
  unfold tailWord_421066
  simp only [CollatzResearch.WordTrace]
  refine ⟨3839384673139317298168763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10238359128371512795116701 3839384673139317298168763)
  ·
    refine ⟨5759077009708975947253145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3839384673139317298168763 5759077009708975947253145)
    ·
      refine ⟨4319307757281731960439859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5759077009708975947253145 4319307757281731960439859)
      ·
        refine ⟨6478961635922597940659789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4319307757281731960439859 6478961635922597940659789)
        ·
          refine ⟨2429610613470974227747421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6478961635922597940659789 2429610613470974227747421)
          ·
            refine ⟨911103980051615335405283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2429610613470974227747421 911103980051615335405283)
            ·
              refine ⟨1366655970077423003107925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 911103980051615335405283 1366655970077423003107925)
              ·
                refine ⟨16015499649344800817671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1366655970077423003107925 16015499649344800817671)
                ·
                  rfl

theorem cell22_421066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 8].length) (baseStart_421066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_421066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_421066 prefixEnd_421066 := by exact prefixLift 421066
  have htrace : WordTrace (prefixWord ++ tailWord_421066) baseStart_421066 baseEnd_421066 := by
    simpa [prefixWord, tailWord_421066, baseEnd_421066] using wordTrace_append hprefix tailTrace_421066
  have hstable : (prefixWord ++ tailWord_421066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421066).length < 2 ^ (prefixWord ++ tailWord_421066).sum := by decide
  have hdescent : baseEnd_421066 < baseStart_421066 := by decide
  rcases family_descends (prefixWord ++ tailWord_421066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421085 : List Nat := [1, 4, 3, 2, 2, 1, 1, 2, 2, 4]
def baseStart_421085 : Nat := 118140960795 + 421085 * 2 ^ 59
def prefixEnd_421085 : Nat := 4983230072969 + 3 ^ 40 * 421085 * 2
def baseEnd_421085 : Nat := 144146000932393491133981

theorem tailTrace_421085 : CollatzResearch.WordTrace tailWord_421085 prefixEnd_421085 144146000932393491133981 := by
  unfold tailWord_421085
  simp only [CollatzResearch.WordTrace]
  refine ⟨15358231679488435437616709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10238821119658956958411139 15358231679488435437616709)
  ·
    refine ⟨2879668439904081644553133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15358231679488435437616709 2879668439904081644553133)
    ·
      refine ⟨1079875664964030616707425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2879668439904081644553133 1079875664964030616707425)
      ·
        refine ⟨809906748723022962530569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1079875664964030616707425 809906748723022962530569)
        ·
          refine ⟨607430061542267221897927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 809906748723022962530569 607430061542267221897927)
          ·
            refine ⟨911145092313400832846891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607430061542267221897927 911145092313400832846891)
            ·
              refine ⟨1366717638470101249270337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 911145092313400832846891 1366717638470101249270337)
              ·
                refine ⟨1025038228852575936952753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1366717638470101249270337 1025038228852575936952753)
                ·
                  refine ⟨768778671639431952714565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1025038228852575936952753 768778671639431952714565)
                  ·
                    refine ⟨144146000932393491133981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 768778671639431952714565 144146000932393491133981)
                    ·
                      rfl

theorem cell22_421085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_421085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_421085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_421085 prefixEnd_421085 := by exact prefixLift 421085
  have htrace : WordTrace (prefixWord ++ tailWord_421085) baseStart_421085 baseEnd_421085 := by
    simpa [prefixWord, tailWord_421085, baseEnd_421085] using wordTrace_append hprefix tailTrace_421085
  have hstable : (prefixWord ++ tailWord_421085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421085).length < 2 ^ (prefixWord ++ tailWord_421085).sum := by decide
  have hdescent : baseEnd_421085 < baseStart_421085 := by decide
  rcases family_descends (prefixWord ++ tailWord_421085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421096 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 2, 6]
def baseStart_421096 : Nat := 118140960795 + 421096 * 2 ^ 59
def prefixEnd_421096 : Nat := 4983230072969 + 3 ^ 40 * 421096 * 2
def baseEnd_421096 : Nat := 144149766457193129108947

theorem tailTrace_421096 : CollatzResearch.WordTrace tailWord_421096 prefixEnd_421096 144149766457193129108947 := by
  unfold tailWord_421096
  simp only [CollatzResearch.WordTrace]
  refine ⟨7679316441224292158133571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10239088588299056210844761 7679316441224292158133571)
  ·
    refine ⟨11518974661836438237200357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7679316441224292158133571 11518974661836438237200357)
    ·
      refine ⟨2159807749094332169475067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11518974661836438237200357 2159807749094332169475067)
      ·
        refine ⟨3239711623641498254212601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2159807749094332169475067 3239711623641498254212601)
        ·
          refine ⟨2429783717731123690659451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3239711623641498254212601 2429783717731123690659451)
          ·
            refine ⟨3644675576596685535989177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2429783717731123690659451 3644675576596685535989177)
            ·
              refine ⟨2733506682447514151991883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3644675576596685535989177 2733506682447514151991883)
              ·
                refine ⟨4100260023671271227987825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2733506682447514151991883 4100260023671271227987825)
                ·
                  refine ⟨3075195017753453420990869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4100260023671271227987825 3075195017753453420990869)
                  ·
                    refine ⟨144149766457193129108947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3075195017753453420990869 144149766457193129108947)
                    ·
                      rfl

theorem cell22_421096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_421096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_421096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_421096 prefixEnd_421096 := by exact prefixLift 421096
  have htrace : WordTrace (prefixWord ++ tailWord_421096) baseStart_421096 baseEnd_421096 := by
    simpa [prefixWord, tailWord_421096, baseEnd_421096] using wordTrace_append hprefix tailTrace_421096
  have hstable : (prefixWord ++ tailWord_421096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421096).length < 2 ^ (prefixWord ++ tailWord_421096).sum := by decide
  have hdescent : baseEnd_421096 < baseStart_421096 := by decide
  rcases family_descends (prefixWord ++ tailWord_421096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421111 : List Nat := [1, 1, 3, 1, 1, 1, 2, 7, 5]
def baseStart_421111 : Nat := 118140960795 + 421111 * 2 ^ 59
def prefixEnd_421111 : Nat := 4983230072969 + 3 ^ 40 * 421111 * 2
def baseEnd_421111 : Nat := 48051633754579363327967

theorem tailTrace_421111 : CollatzResearch.WordTrace tailWord_421111 prefixEnd_421111 48051633754579363327967 := by
  unfold tailWord_421111
  simp only [CollatzResearch.WordTrace]
  refine ⟨15359179977394241878063187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10239453318262827918708791 15359179977394241878063187)
  ·
    refine ⟨23038769966091362817094781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15359179977394241878063187 23038769966091362817094781)
    ·
      refine ⟨8639538737284261056410543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23038769966091362817094781 8639538737284261056410543)
      ·
        refine ⟨12959308105926391584615815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8639538737284261056410543 12959308105926391584615815)
        ·
          refine ⟨19438962158889587376923723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12959308105926391584615815 19438962158889587376923723)
          ·
            refine ⟨29158443238334381065385585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19438962158889587376923723 29158443238334381065385585)
            ·
              refine ⟨21868832428750785799039189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29158443238334381065385585 21868832428750785799039189)
              ·
                refine ⟨512550760048846542164981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 21868832428750785799039189 512550760048846542164981)
                ·
                  refine ⟨48051633754579363327967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 512550760048846542164981 48051633754579363327967)
                  ·
                    rfl

theorem cell22_421111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 5].length) (baseStart_421111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_421111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_421111 prefixEnd_421111 := by exact prefixLift 421111
  have htrace : WordTrace (prefixWord ++ tailWord_421111) baseStart_421111 baseEnd_421111 := by
    simpa [prefixWord, tailWord_421111, baseEnd_421111] using wordTrace_append hprefix tailTrace_421111
  have hstable : (prefixWord ++ tailWord_421111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421111).length < 2 ^ (prefixWord ++ tailWord_421111).sum := by decide
  have hdescent : baseEnd_421111 < baseStart_421111 := by decide
  rcases family_descends (prefixWord ++ tailWord_421111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421149 : List Nat := [1, 4, 2, 3, 1, 1, 4, 2, 1, 3]
def baseStart_421149 : Nat := 118140960795 + 421149 * 2 ^ 59
def prefixEnd_421149 : Nat := 4983230072969 + 3 ^ 40 * 421149 * 2
def baseEnd_421149 : Nat := 144167909440318657533785

theorem tailTrace_421149 : CollatzResearch.WordTrace tailWord_421149 prefixEnd_421149 144167909440318657533785 := by
  unfold tailWord_421149
  simp only [CollatzResearch.WordTrace]
  refine ⟨15360565951256574367946501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10240377300837716245297667 15360565951256574367946501)
  ·
    refine ⟨2880106115860607693989969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15360565951256574367946501 2880106115860607693989969)
    ·
      refine ⟨2160079586895455770492477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2880106115860607693989969 2160079586895455770492477)
      ·
        refine ⟨810029845085795913934679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2160079586895455770492477 810029845085795913934679)
        ·
          refine ⟨1215044767628693870902019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 810029845085795913934679 1215044767628693870902019)
          ·
            refine ⟨1822567151443040806353029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1215044767628693870902019 1822567151443040806353029)
            ·
              refine ⟨341731340895570151191193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1822567151443040806353029 341731340895570151191193)
              ·
                refine ⟨256298505671677613393395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 341731340895570151191193 256298505671677613393395)
                ·
                  refine ⟨384447758507516420090093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 256298505671677613393395 384447758507516420090093)
                  ·
                    refine ⟨144167909440318657533785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 384447758507516420090093 144167909440318657533785)
                    ·
                      rfl

theorem cell22_421149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_421149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_421149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_421149 prefixEnd_421149 := by exact prefixLift 421149
  have htrace : WordTrace (prefixWord ++ tailWord_421149) baseStart_421149 baseEnd_421149 := by
    simpa [prefixWord, tailWord_421149, baseEnd_421149] using wordTrace_append hprefix tailTrace_421149
  have hstable : (prefixWord ++ tailWord_421149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421149).length < 2 ^ (prefixWord ++ tailWord_421149).sum := by decide
  have hdescent : baseEnd_421149 < baseStart_421149 := by decide
  rcases family_descends (prefixWord ++ tailWord_421149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421173 : List Nat := [1, 3, 3, 1, 2, 3, 1, 2, 6]
def baseStart_421173 : Nat := 118140960795 + 421173 * 2 ^ 59
def prefixEnd_421173 : Nat := 4983230072969 + 3 ^ 40 * 421173 * 2
def baseEnd_421173 : Nat := 48058708376930198311237

theorem tailTrace_421173 : CollatzResearch.WordTrace tailWord_421173 prefixEnd_421173 48058708376930198311237 := by
  unfold tailWord_421173
  simp only [CollatzResearch.WordTrace]
  refine ⟨15361441303169626466820173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10240960868779750977880115 15361441303169626466820173)
  ·
    refine ⟨5760540488688609925057565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15361441303169626466820173 5760540488688609925057565)
    ·
      refine ⟨2160202683258228721896587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5760540488688609925057565 2160202683258228721896587)
      ·
        refine ⟨3240304024887343082844881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2160202683258228721896587 3240304024887343082844881)
        ·
          refine ⟨2430228018665507312133661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3240304024887343082844881 2430228018665507312133661)
          ·
            refine ⟨911335506999565242050123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2430228018665507312133661 911335506999565242050123)
            ·
              refine ⟨1367003260499347863075185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 911335506999565242050123 1367003260499347863075185)
              ·
                refine ⟨1025252445374510897306389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1367003260499347863075185 1025252445374510897306389)
                ·
                  refine ⟨48058708376930198311237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1025252445374510897306389 48058708376930198311237)
                  ·
                    rfl

theorem cell22_421173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 6].length) (baseStart_421173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_421173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_421173 prefixEnd_421173 := by exact prefixLift 421173
  have htrace : WordTrace (prefixWord ++ tailWord_421173) baseStart_421173 baseEnd_421173 := by
    simpa [prefixWord, tailWord_421173, baseEnd_421173] using wordTrace_append hprefix tailTrace_421173
  have hstable : (prefixWord ++ tailWord_421173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421173).length < 2 ^ (prefixWord ++ tailWord_421173).sum := by decide
  have hdescent : baseEnd_421173 < baseStart_421173 := by decide
  rcases family_descends (prefixWord ++ tailWord_421173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421201 : List Nat := [1, 2, 2, 1, 4, 1, 11]
def baseStart_421201 : Nat := 118140960795 + 421201 * 2 ^ 59
def prefixEnd_421201 : Nat := 4983230072969 + 3 ^ 40 * 421201 * 2
def baseEnd_421201 : Nat := 5340211485296587230875

theorem tailTrace_421201 : CollatzResearch.WordTrace tailWord_421201 prefixEnd_421201 5340211485296587230875 := by
  unfold tailWord_421201
  simp only [CollatzResearch.WordTrace]
  refine ⟨15362462547068187248839457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10241641698045458165892971 15362462547068187248839457)
  ·
    refine ⟨11521846910301140436629593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15362462547068187248839457 11521846910301140436629593)
    ·
      refine ⟨8641385182725855327472195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11521846910301140436629593 8641385182725855327472195)
      ·
        refine ⟨12962077774088782991208293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8641385182725855327472195 12962077774088782991208293)
        ·
          refine ⟨2430389582641646810851555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12962077774088782991208293 2430389582641646810851555)
          ·
            refine ⟨3645584373962470216277333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2430389582641646810851555 3645584373962470216277333)
            ·
              refine ⟨5340211485296587230875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 3645584373962470216277333 5340211485296587230875)
              ·
                rfl

theorem cell22_421201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 11].length) (baseStart_421201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_421201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_421201 prefixEnd_421201 := by exact prefixLift 421201
  have htrace : WordTrace (prefixWord ++ tailWord_421201) baseStart_421201 baseEnd_421201 := by
    simpa [prefixWord, tailWord_421201, baseEnd_421201] using wordTrace_append hprefix tailTrace_421201
  have hstable : (prefixWord ++ tailWord_421201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421201).length < 2 ^ (prefixWord ++ tailWord_421201).sum := by decide
  have hdescent : baseEnd_421201 < baseStart_421201 := by decide
  rcases family_descends (prefixWord ++ tailWord_421201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421205 : List Nat := [1, 3, 2, 2, 3, 2, 1, 1, 4, 3]
def baseStart_421205 : Nat := 118140960795 + 421205 * 2 ^ 59
def prefixEnd_421205 : Nat := 4983230072969 + 3 ^ 40 * 421205 * 2
def baseEnd_421205 : Nat := 144187079384753178133613

theorem tailTrace_421205 : CollatzResearch.WordTrace tailWord_421205 prefixEnd_421205 144187079384753178133613 := by
  unfold tailWord_421205
  simp only [CollatzResearch.WordTrace]
  refine ⟨15362608439053695931985069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10241738959369130621323379 15362608439053695931985069)
  ·
    refine ⟨5760978164645135974494401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15362608439053695931985069 5760978164645135974494401)
    ·
      refine ⟨4320733623483851980870801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5760978164645135974494401 4320733623483851980870801)
      ·
        refine ⟨3240550217612888985653101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4320733623483851980870801 3240550217612888985653101)
        ·
          refine ⟨1215206331604833369619913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3240550217612888985653101 1215206331604833369619913)
          ·
            refine ⟨911404748703625027214935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1215206331604833369619913 911404748703625027214935)
            ·
              refine ⟨1367107123055437540822403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 911404748703625027214935 1367107123055437540822403)
              ·
                refine ⟨2050660684583156311233605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1367107123055437540822403 2050660684583156311233605)
                ·
                  refine ⟨384498878359341808356301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2050660684583156311233605 384498878359341808356301)
                  ·
                    refine ⟨144187079384753178133613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 384498878359341808356301 144187079384753178133613)
                    ·
                      rfl

theorem cell22_421205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_421205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_421205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_421205 prefixEnd_421205 := by exact prefixLift 421205
  have htrace : WordTrace (prefixWord ++ tailWord_421205) baseStart_421205 baseEnd_421205 := by
    simpa [prefixWord, tailWord_421205, baseEnd_421205] using wordTrace_append hprefix tailTrace_421205
  have hstable : (prefixWord ++ tailWord_421205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421205).length < 2 ^ (prefixWord ++ tailWord_421205).sum := by decide
  have hdescent : baseEnd_421205 < baseStart_421205 := by decide
  rcases family_descends (prefixWord ++ tailWord_421205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421218 : List Nat := [3, 3, 2, 1, 1, 1, 2, 9]
def baseStart_421218 : Nat := 118140960795 + 421218 * 2 ^ 59
def prefixEnd_421218 : Nat := 4983230072969 + 3 ^ 40 * 421218 * 2
def baseEnd_421218 : Nat := 16021281061158386395397

theorem tailTrace_421218 : CollatzResearch.WordTrace tailWord_421218 prefixEnd_421218 16021281061158386395397 := by
  unfold tailWord_421218
  simp only [CollatzResearch.WordTrace]
  refine ⟨3840770647001649788052077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10242055058671066101472205 3840770647001649788052077)
  ·
    refine ⟨1440288992625618670519529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3840770647001649788052077 1440288992625618670519529)
    ·
      refine ⟨1080216744469214002889647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1440288992625618670519529 1080216744469214002889647)
      ·
        refine ⟨1620325116703821004334471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1080216744469214002889647 1620325116703821004334471)
        ·
          refine ⟨2430487675055731506501707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1620325116703821004334471 2430487675055731506501707)
          ·
            refine ⟨3645731512583597259752561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2430487675055731506501707 3645731512583597259752561)
            ·
              refine ⟨2734298634437697944814421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3645731512583597259752561 2734298634437697944814421)
              ·
                refine ⟨16021281061158386395397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2734298634437697944814421 16021281061158386395397)
                ·
                  rfl

theorem cell22_421218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 9].length) (baseStart_421218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_421218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_421218 prefixEnd_421218 := by exact prefixLift 421218
  have htrace : WordTrace (prefixWord ++ tailWord_421218) baseStart_421218 baseEnd_421218 := by
    simpa [prefixWord, tailWord_421218, baseEnd_421218] using wordTrace_append hprefix tailTrace_421218
  have hstable : (prefixWord ++ tailWord_421218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421218).length < 2 ^ (prefixWord ++ tailWord_421218).sum := by decide
  have hdescent : baseEnd_421218 < baseStart_421218 := by decide
  rcases family_descends (prefixWord ++ tailWord_421218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421436 : List Nat := [2, 2, 2, 2, 5, 1, 1, 1, 3, 3]
def baseStart_421436 : Nat := 118140960795 + 421436 * 2 ^ 59
def prefixEnd_421436 : Nat := 4983230072969 + 3 ^ 40 * 421436 * 2
def baseEnd_421436 : Nat := 144266155405545575607905

theorem tailTrace_421436 : CollatzResearch.WordTrace tailWord_421436 prefixEnd_421436 144266155405545575607905 := by
  unfold tailWord_421436
  simp only [CollatzResearch.WordTrace]
  refine ⟨7685516850608411191822081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10247355800811214922429441 7685516850608411191822081)
  ·
    refine ⟨5764137637956308393866561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7685516850608411191822081 5764137637956308393866561)
    ·
      refine ⟨4323103228467231295399921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5764137637956308393866561 4323103228467231295399921)
      ·
        refine ⟨3242327421350423471549941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4323103228467231295399921 3242327421350423471549941)
        ·
          refine ⟨303968195751602200457807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3242327421350423471549941 303968195751602200457807)
          ·
            refine ⟨455952293627403300686711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303968195751602200457807 455952293627403300686711)
            ·
              refine ⟨683928440441104951030067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 455952293627403300686711 683928440441104951030067)
              ·
                refine ⟨1025892660661657426545101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 683928440441104951030067 1025892660661657426545101)
                ·
                  refine ⟨384709747748121534954413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1025892660661657426545101 384709747748121534954413)
                  ·
                    refine ⟨144266155405545575607905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 384709747748121534954413 144266155405545575607905)
                    ·
                      rfl

theorem cell22_421436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_421436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_421436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_421436 prefixEnd_421436 := by exact prefixLift 421436
  have htrace : WordTrace (prefixWord ++ tailWord_421436) baseStart_421436 baseEnd_421436 := by
    simpa [prefixWord, tailWord_421436, baseEnd_421436] using wordTrace_append hprefix tailTrace_421436
  have hstable : (prefixWord ++ tailWord_421436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421436).length < 2 ^ (prefixWord ++ tailWord_421436).sum := by decide
  have hdescent : baseEnd_421436 < baseStart_421436 := by decide
  rcases family_descends (prefixWord ++ tailWord_421436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421445 : List Nat := [1, 3, 1, 1, 1, 4, 2, 2, 3, 4]
def baseStart_421445 : Nat := 118140960795 + 421445 * 2 ^ 59
def prefixEnd_421445 : Nat := 4983230072969 + 3 ^ 40 * 421445 * 2
def baseEnd_421445 : Nat := 144269236289472552132877

theorem tailTrace_421445 : CollatzResearch.WordTrace tailWord_421445 prefixEnd_421445 144269236289472552132877 := by
  unfold tailWord_421445
  simp only [CollatzResearch.WordTrace]
  refine ⟨15371361958184216920721789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10247574638789477947147859 15371361958184216920721789)
  ·
    refine ⟨5764260734319081345270671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15371361958184216920721789 5764260734319081345270671)
    ·
      refine ⟨8646391101478622017906007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5764260734319081345270671 8646391101478622017906007)
      ·
        refine ⟨12969586652217933026859011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8646391101478622017906007 12969586652217933026859011)
        ·
          refine ⟨19454379978326899540288517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12969586652217933026859011 19454379978326899540288517)
          ·
            refine ⟨3647696245936293663804097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19454379978326899540288517 3647696245936293663804097)
            ·
              refine ⟨2735772184452220247853073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3647696245936293663804097 2735772184452220247853073)
              ·
                refine ⟨2051829138339165185889805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2735772184452220247853073 2051829138339165185889805)
                ·
                  refine ⟨769435926877186944708677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2051829138339165185889805 769435926877186944708677)
                  ·
                    refine ⟨144269236289472552132877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 769435926877186944708677 144269236289472552132877)
                    ·
                      rfl

theorem cell22_421445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_421445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_421445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_421445 prefixEnd_421445 := by exact prefixLift 421445
  have htrace : WordTrace (prefixWord ++ tailWord_421445) baseStart_421445 baseEnd_421445 := by
    simpa [prefixWord, tailWord_421445, baseEnd_421445] using wordTrace_append hprefix tailTrace_421445
  have hstable : (prefixWord ++ tailWord_421445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421445).length < 2 ^ (prefixWord ++ tailWord_421445).sum := by decide
  have hdescent : baseEnd_421445 < baseStart_421445 := by decide
  rcases family_descends (prefixWord ++ tailWord_421445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421460 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 8]
def baseStart_421460 : Nat := 118140960795 + 421460 * 2 ^ 59
def prefixEnd_421460 : Nat := 4983230072969 + 3 ^ 40 * 421460 * 2
def baseEnd_421460 : Nat := 48091457032005837669277

theorem tailTrace_421460 : CollatzResearch.WordTrace tailWord_421460 prefixEnd_421460 48091457032005837669277 := by
  unfold tailWord_421460
  simp only [CollatzResearch.WordTrace]
  refine ⟨7685954526564937241258917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10247939368753249655011889 7685954526564937241258917)
  ·
    refine ⟨1441116473730925732736047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7685954526564937241258917 1441116473730925732736047)
    ·
      refine ⟨2161674710596388599104071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1441116473730925732736047 2161674710596388599104071)
      ·
        refine ⟨3242512065894582898656107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2161674710596388599104071 3242512065894582898656107)
        ·
          refine ⟨4863768098841874347984161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3242512065894582898656107 4863768098841874347984161)
          ·
            refine ⟨3647826074131405760988121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4863768098841874347984161 3647826074131405760988121)
            ·
              refine ⟨2735869555598554320741091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3647826074131405760988121 2735869555598554320741091)
              ·
                refine ⟨4103804333397831481111637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2735869555598554320741091 4103804333397831481111637)
                ·
                  refine ⟨48091457032005837669277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4103804333397831481111637 48091457032005837669277)
                  ·
                    rfl

theorem cell22_421460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_421460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_421460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_421460 prefixEnd_421460 := by exact prefixLift 421460
  have htrace : WordTrace (prefixWord ++ tailWord_421460) baseStart_421460 baseEnd_421460 := by
    simpa [prefixWord, tailWord_421460, baseEnd_421460] using wordTrace_append hprefix tailTrace_421460
  have hstable : (prefixWord ++ tailWord_421460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421460).length < 2 ^ (prefixWord ++ tailWord_421460).sum := by decide
  have hdescent : baseEnd_421460 < baseStart_421460 := by decide
  rcases family_descends (prefixWord ++ tailWord_421460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421475 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 3, 5]
def baseStart_421475 : Nat := 118140960795 + 421475 * 2 ^ 59
def prefixEnd_421475 : Nat := 4983230072969 + 3 ^ 40 * 421475 * 2
def baseEnd_421475 : Nat := 144279505902562473882785

theorem tailTrace_421475 : CollatzResearch.WordTrace tailWord_421475 prefixEnd_421475 144279505902562473882785 := by
  unfold tailWord_421475
  simp only [CollatzResearch.WordTrace]
  refine ⟨15372456148075532044313879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10248304098717021362875919 15372456148075532044313879)
  ·
    refine ⟨23058684222113298066470819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15372456148075532044313879 23058684222113298066470819)
    ·
      refine ⟨34588026333169947099706229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23058684222113298066470819 34588026333169947099706229)
      ·
        refine ⟨3242627468734682540597459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34588026333169947099706229 3242627468734682540597459)
        ·
          refine ⟨4863941203102023810896189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3242627468734682540597459 4863941203102023810896189)
          ·
            refine ⟨1823977951163258929086071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4863941203102023810896189 1823977951163258929086071)
            ·
              refine ⟨2735966926744888393629107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1823977951163258929086071 2735966926744888393629107)
              ·
                refine ⟨4103950390117332590443661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2735966926744888393629107 4103950390117332590443661)
                ·
                  refine ⟨1538981396293999721416373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4103950390117332590443661 1538981396293999721416373)
                  ·
                    refine ⟨144279505902562473882785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1538981396293999721416373 144279505902562473882785)
                    ·
                      rfl

theorem cell22_421475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 5].length) (baseStart_421475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_421475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_421475 prefixEnd_421475 := by exact prefixLift 421475
  have htrace : WordTrace (prefixWord ++ tailWord_421475) baseStart_421475 baseEnd_421475 := by
    simpa [prefixWord, tailWord_421475, baseEnd_421475] using wordTrace_append hprefix tailTrace_421475
  have hstable : (prefixWord ++ tailWord_421475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421475).length < 2 ^ (prefixWord ++ tailWord_421475).sum := by decide
  have hdescent : baseEnd_421475 < baseStart_421475 := by decide
  rcases family_descends (prefixWord ++ tailWord_421475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421524 : List Nat := [2, 4, 2, 2, 2, 1, 1, 1, 1, 6]
def baseStart_421524 : Nat := 118140960795 + 421524 * 2 ^ 59
def prefixEnd_421524 : Nat := 4983230072969 + 3 ^ 40 * 421524 * 2
def baseEnd_421524 : Nat := 144296279603942679407635

theorem tailTrace_421524 : CollatzResearch.WordTrace tailWord_421524 prefixEnd_421524 144296279603942679407635 := by
  unfold tailWord_421524
  simp only [CollatzResearch.WordTrace]
  refine ⟨7687121662449006706423813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10249495549932008941898417 7687121662449006706423813)
  ·
    refine ⟨1441335311709188757454465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7687121662449006706423813 1441335311709188757454465)
    ·
      refine ⟨1081001483781891568090849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1441335311709188757454465 1081001483781891568090849)
      ·
        refine ⟨810751112836418676068137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1081001483781891568090849 810751112836418676068137)
        ·
          refine ⟨608063334627314007051103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 810751112836418676068137 608063334627314007051103)
          ·
            refine ⟨912095001940971010576655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 608063334627314007051103 912095001940971010576655)
            ·
              refine ⟨1368142502911456515864983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 912095001940971010576655 1368142502911456515864983)
              ·
                refine ⟨2052213754367184773797475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1368142502911456515864983 2052213754367184773797475)
                ·
                  refine ⟨3078320631550777160696213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2052213754367184773797475 3078320631550777160696213)
                  ·
                    refine ⟨144296279603942679407635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3078320631550777160696213 144296279603942679407635)
                    ·
                      rfl

theorem cell22_421524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_421524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_421524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_421524 prefixEnd_421524 := by exact prefixLift 421524
  have htrace : WordTrace (prefixWord ++ tailWord_421524) baseStart_421524 baseEnd_421524 := by
    simpa [prefixWord, tailWord_421524, baseEnd_421524] using wordTrace_append hprefix tailTrace_421524
  have hstable : (prefixWord ++ tailWord_421524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421524).length < 2 ^ (prefixWord ++ tailWord_421524).sum := by decide
  have hdescent : baseEnd_421524 < baseStart_421524 := by decide
  rcases family_descends (prefixWord ++ tailWord_421524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421588 : List Nat := [2, 4, 1, 3, 1, 1, 3, 3, 1, 3]
def baseStart_421588 : Nat := 118140960795 + 421588 * 2 ^ 59
def prefixEnd_421588 : Nat := 4983230072969 + 3 ^ 40 * 421588 * 2
def baseEnd_421588 : Nat := 144318188111867845807439

theorem tailTrace_421588 : CollatzResearch.WordTrace tailWord_421588 prefixEnd_421588 144318188111867845807439 := by
  unfold tailWord_421588
  simp only [CollatzResearch.WordTrace]
  refine ⟨7688288798333076171588709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10251051731110768228784945 7688288798333076171588709)
  ·
    refine ⟨1441554149687451782172883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7688288798333076171588709 1441554149687451782172883)
    ·
      refine ⟨2162331224531177673259325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1441554149687451782172883 2162331224531177673259325)
      ·
        refine ⟨810874209199191627472247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2162331224531177673259325 810874209199191627472247)
        ·
          refine ⟨1216311313798787441208371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 810874209199191627472247 1216311313798787441208371)
          ·
            refine ⟨1824466970698181161812557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1216311313798787441208371 1824466970698181161812557)
            ·
              refine ⟨684175114011817935679709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1824466970698181161812557 684175114011817935679709)
              ·
                refine ⟨256565667754431725879891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 684175114011817935679709 256565667754431725879891)
                ·
                  refine ⟨384848501631647588819837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 256565667754431725879891 384848501631647588819837)
                  ·
                    refine ⟨144318188111867845807439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 384848501631647588819837 144318188111867845807439)
                    ·
                      rfl

theorem cell22_421588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_421588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_421588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_421588 prefixEnd_421588 := by exact prefixLift 421588
  have htrace : WordTrace (prefixWord ++ tailWord_421588) baseStart_421588 baseEnd_421588 := by
    simpa [prefixWord, tailWord_421588, baseEnd_421588] using wordTrace_append hprefix tailTrace_421588
  have hstable : (prefixWord ++ tailWord_421588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421588).length < 2 ^ (prefixWord ++ tailWord_421588).sum := by decide
  have hdescent : baseEnd_421588 < baseStart_421588 := by decide
  rcases family_descends (prefixWord ++ tailWord_421588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421612 : List Nat := [2, 2, 1, 1, 2, 2, 5, 1, 6]
def baseStart_421612 : Nat := 118140960795 + 421612 * 2 ^ 59
def prefixEnd_421612 : Nat := 4983230072969 + 3 ^ 40 * 421612 * 2
def baseEnd_421612 : Nat := 48108801267446594402455

theorem tailTrace_421612 : CollatzResearch.WordTrace tailWord_421612 prefixEnd_421612 48108801267446594402455 := by
  unfold tailWord_421612
  simp only [CollatzResearch.WordTrace]
  refine ⟨7688726474289602221025545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10251635299052802961367393 7688726474289602221025545)
  ·
    refine ⟨5766544855717201665769159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7688726474289602221025545 5766544855717201665769159)
    ·
      refine ⟨8649817283575802498653739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5766544855717201665769159 8649817283575802498653739)
      ·
        refine ⟨12974725925363703747980609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8649817283575802498653739 12974725925363703747980609)
        ·
          refine ⟨9731044444022777810985457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12974725925363703747980609 9731044444022777810985457)
          ·
            refine ⟨7298283333017083358239093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9731044444022777810985457 7298283333017083358239093)
            ·
              refine ⟨684214062470351564834915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7298283333017083358239093 684214062470351564834915)
              ·
                refine ⟨1026321093705527347252373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 684214062470351564834915 1026321093705527347252373)
                ·
                  refine ⟨48108801267446594402455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1026321093705527347252373 48108801267446594402455)
                  ·
                    rfl

theorem cell22_421612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 6].length) (baseStart_421612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_421612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_421612 prefixEnd_421612 := by exact prefixLift 421612
  have htrace : WordTrace (prefixWord ++ tailWord_421612) baseStart_421612 baseEnd_421612 := by
    simpa [prefixWord, tailWord_421612, baseEnd_421612] using wordTrace_append hprefix tailTrace_421612
  have hstable : (prefixWord ++ tailWord_421612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421612).length < 2 ^ (prefixWord ++ tailWord_421612).sum := by decide
  have hdescent : baseEnd_421612 < baseStart_421612 := by decide
  rcases family_descends (prefixWord ++ tailWord_421612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421627 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 6, 3]
def baseStart_421627 : Nat := 118140960795 + 421627 * 2 ^ 59
def prefixEnd_421627 : Nat := 4983230072969 + 3 ^ 40 * 421627 * 2
def baseEnd_421627 : Nat := 144331538608884744082319

theorem tailTrace_421627 : CollatzResearch.WordTrace tailWord_421627 prefixEnd_421627 144331538608884744082319 := by
  unfold tailWord_421627
  simp only [CollatzResearch.WordTrace]
  refine ⟨15378000043524862003847135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10252000029016574669231423 15378000043524862003847135)
  ·
    refine ⟨23067000065287293005770703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15378000043524862003847135 23067000065287293005770703)
    ·
      refine ⟨34600500097930939508656055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23067000065287293005770703 34600500097930939508656055)
      ·
        refine ⟨51900750146896409262984083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34600500097930939508656055 51900750146896409262984083)
        ·
          refine ⟨77851125220344613894476125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51900750146896409262984083 77851125220344613894476125)
          ·
            refine ⟨29194171957629230210428547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77851125220344613894476125 29194171957629230210428547)
            ·
              refine ⟨43791257936443845315642821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29194171957629230210428547 43791257936443845315642821)
              ·
                refine ⟨8210860863083220996683029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43791257936443845315642821 8210860863083220996683029)
                ·
                  refine ⟨384884102957025984219517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8210860863083220996683029 384884102957025984219517)
                  ·
                    refine ⟨144331538608884744082319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 384884102957025984219517 144331538608884744082319)
                    ·
                      rfl

theorem cell22_421627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 6, 3].length) (baseStart_421627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_421627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_421627 prefixEnd_421627 := by exact prefixLift 421627
  have htrace : WordTrace (prefixWord ++ tailWord_421627) baseStart_421627 baseEnd_421627 := by
    simpa [prefixWord, tailWord_421627, baseEnd_421627] using wordTrace_append hprefix tailTrace_421627
  have hstable : (prefixWord ++ tailWord_421627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421627).length < 2 ^ (prefixWord ++ tailWord_421627).sum := by decide
  have hdescent : baseEnd_421627 < baseStart_421627 := by decide
  rcases family_descends (prefixWord ++ tailWord_421627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421719 : List Nat := [1, 1, 3, 2, 5, 1, 1, 1, 7]
def baseStart_421719 : Nat := 118140960795 + 421719 * 2 ^ 59
def prefixEnd_421719 : Nat := 4983230072969 + 3 ^ 40 * 421719 * 2
def baseEnd_421719 : Nat := 48121010696342390260679

theorem tailTrace_421719 : CollatzResearch.WordTrace tailWord_421719 prefixEnd_421719 48121010696342390260679 := by
  unfold tailWord_421719
  simp only [CollatzResearch.WordTrace]
  refine ⟨15381355559191561716196211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10254237039461041144130807 15381355559191561716196211)
  ·
    refine ⟨23072033338787342574294317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15381355559191561716196211 23072033338787342574294317)
    ·
      refine ⟨8652012502045253465360369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23072033338787342574294317 8652012502045253465360369)
      ·
        refine ⟨6489009376533940099020277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8652012502045253465360369 6489009376533940099020277)
        ·
          refine ⟨608344629050056884283151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6489009376533940099020277 608344629050056884283151)
          ·
            refine ⟨912516943575085326424727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 608344629050056884283151 912516943575085326424727)
            ·
              refine ⟨1368775415362627989637091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 912516943575085326424727 1368775415362627989637091)
              ·
                refine ⟨2053163123043941984455637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1368775415362627989637091 2053163123043941984455637)
                ·
                  refine ⟨48121010696342390260679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2053163123043941984455637 48121010696342390260679)
                  ·
                    rfl

theorem cell22_421719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 7].length) (baseStart_421719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_421719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_421719 prefixEnd_421719 := by exact prefixLift 421719
  have htrace : WordTrace (prefixWord ++ tailWord_421719) baseStart_421719 baseEnd_421719 := by
    simpa [prefixWord, tailWord_421719, baseEnd_421719] using wordTrace_append hprefix tailTrace_421719
  have hstable : (prefixWord ++ tailWord_421719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421719).length < 2 ^ (prefixWord ++ tailWord_421719).sum := by decide
  have hdescent : baseEnd_421719 < baseStart_421719 := by decide
  rcases family_descends (prefixWord ++ tailWord_421719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421736 : List Nat := [2, 1, 4, 2, 1, 1, 5, 1, 5]
def baseStart_421736 : Nat := 118140960795 + 421736 * 2 ^ 59
def prefixEnd_421736 : Nat := 4983230072969 + 3 ^ 40 * 421736 * 2
def baseEnd_421736 : Nat := 48122950512148264368995

theorem tailTrace_421736 : CollatzResearch.WordTrace tailWord_421736 prefixEnd_421736 48122950512148264368995 := by
  unfold tailWord_421736
  simp only [CollatzResearch.WordTrace]
  refine ⟨7690987800064986809782531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10254650400086649079710041 7690987800064986809782531)
  ·
    refine ⟨11536481700097480214673797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7690987800064986809782531 11536481700097480214673797)
    ·
      refine ⟨2163090318768277540251337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11536481700097480214673797 2163090318768277540251337)
      ·
        refine ⟨1622317739076208155188503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2163090318768277540251337 1622317739076208155188503)
        ·
          refine ⟨2433476608614312232782755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1622317739076208155188503 2433476608614312232782755)
          ·
            refine ⟨3650214912921468349174133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2433476608614312232782755 3650214912921468349174133)
            ·
              refine ⟨342207648086387657735075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3650214912921468349174133 342207648086387657735075)
              ·
                refine ⟨513311472129581486602613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 342207648086387657735075 513311472129581486602613)
                ·
                  refine ⟨48122950512148264368995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 513311472129581486602613 48122950512148264368995)
                  ·
                    rfl

theorem cell22_421736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 5].length) (baseStart_421736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_421736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_421736 prefixEnd_421736 := by exact prefixLift 421736
  have htrace : WordTrace (prefixWord ++ tailWord_421736) baseStart_421736 baseEnd_421736 := by
    simpa [prefixWord, tailWord_421736, baseEnd_421736] using wordTrace_append hprefix tailTrace_421736
  have hstable : (prefixWord ++ tailWord_421736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421736).length < 2 ^ (prefixWord ++ tailWord_421736).sum := by decide
  have hdescent : baseEnd_421736 < baseStart_421736 := by decide
  rcases family_descends (prefixWord ++ tailWord_421736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421809 : List Nat := [1, 2, 2, 4, 2, 1, 2, 8]
def baseStart_421809 : Nat := 118140960795 + 421809 * 2 ^ 59
def prefixEnd_421809 : Nat := 4983230072969 + 3 ^ 40 * 421809 * 2
def baseEnd_421809 : Nat := 16043760103144104003529

theorem tailTrace_421809 : CollatzResearch.WordTrace tailWord_421809 prefixEnd_421809 16043760103144104003529 := by
  unfold tailWord_421809
  simp only [CollatzResearch.WordTrace]
  refine ⟨15384638128865507086972481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10256425419243671391314987 15384638128865507086972481)
  ·
    refine ⟨11538478596649130315229361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15384638128865507086972481 11538478596649130315229361)
    ·
      refine ⟨8653858947486847736422021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11538478596649130315229361 8653858947486847736422021)
      ·
        refine ⟨1622598552653783950579129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8653858947486847736422021 1622598552653783950579129)
        ·
          refine ⟨1216948914490337962934347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1622598552653783950579129 1216948914490337962934347)
          ·
            refine ⟨1825423371735506944401521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1216948914490337962934347 1825423371735506944401521)
            ·
              refine ⟨1369067528801630208301141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1825423371735506944401521 1369067528801630208301141)
              ·
                refine ⟨16043760103144104003529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1369067528801630208301141 16043760103144104003529)
                ·
                  rfl

theorem cell22_421809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 8].length) (baseStart_421809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_421809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_421809 prefixEnd_421809 := by exact prefixLift 421809
  have htrace : WordTrace (prefixWord ++ tailWord_421809) baseStart_421809 baseEnd_421809 := by
    simpa [prefixWord, tailWord_421809, baseEnd_421809] using wordTrace_append hprefix tailTrace_421809
  have hstable : (prefixWord ++ tailWord_421809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421809).length < 2 ^ (prefixWord ++ tailWord_421809).sum := by decide
  have hdescent : baseEnd_421809 < baseStart_421809 := by decide
  rcases family_descends (prefixWord ++ tailWord_421809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421916 : List Nat := [2, 2, 3, 1, 3, 1, 2, 2, 6]
def baseStart_421916 : Nat := 118140960795 + 421916 * 2 ^ 59
def prefixEnd_421916 : Nat := 4983230072969 + 3 ^ 40 * 421916 * 2
def baseEnd_421916 : Nat := 48143489738328107868811

theorem tailTrace_421916 : CollatzResearch.WordTrace tailWord_421916 prefixEnd_421916 48143489738328107868811 := by
  unfold tailWord_421916
  simp only [CollatzResearch.WordTrace]
  refine ⟨7694270369738932180558801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10259027159651909574078401 7694270369738932180558801)
  ·
    refine ⟨5770702777304199135419101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7694270369738932180558801 5770702777304199135419101)
    ·
      refine ⟨2164013541489074675782163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5770702777304199135419101 2164013541489074675782163)
      ·
        refine ⟨3246020312233612013673245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2164013541489074675782163 3246020312233612013673245)
        ·
          refine ⟨1217257617087604505127467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3246020312233612013673245 1217257617087604505127467)
          ·
            refine ⟨1825886425631406757691201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1217257617087604505127467 1825886425631406757691201)
            ·
              refine ⟨1369414819223555068268401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1825886425631406757691201 1369414819223555068268401)
              ·
                refine ⟨1027061114417666301201301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1369414819223555068268401 1027061114417666301201301)
                ·
                  refine ⟨48143489738328107868811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1027061114417666301201301 48143489738328107868811)
                  ·
                    rfl

theorem cell22_421916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 6].length) (baseStart_421916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_421916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_421916 prefixEnd_421916 := by exact prefixLift 421916
  have htrace : WordTrace (prefixWord ++ tailWord_421916) baseStart_421916 baseEnd_421916 := by
    simpa [prefixWord, tailWord_421916, baseEnd_421916] using wordTrace_append hprefix tailTrace_421916
  have hstable : (prefixWord ++ tailWord_421916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421916).length < 2 ^ (prefixWord ++ tailWord_421916).sum := by decide
  have hdescent : baseEnd_421916 < baseStart_421916 := by decide
  rcases family_descends (prefixWord ++ tailWord_421916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421948 : List Nat := [2, 2, 2, 2, 2, 1, 2, 4, 2, 3]
def baseStart_421948 : Nat := 118140960795 + 421948 * 2 ^ 59
def prefixEnd_421948 : Nat := 4983230072969 + 3 ^ 40 * 421948 * 2
def baseEnd_421948 : Nat := 144441423468946906806335

theorem tailTrace_421948 : CollatzResearch.WordTrace tailWord_421948 prefixEnd_421948 144441423468946906806335 := by
  unfold tailWord_421948
  simp only [CollatzResearch.WordTrace]
  refine ⟨7694853937680966913141249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10259805250241289217521665 7694853937680966913141249)
  ·
    refine ⟨5771140453260725184855937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7694853937680966913141249 5771140453260725184855937)
    ·
      refine ⟨4328355339945543888641953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5771140453260725184855937 4328355339945543888641953)
      ·
        refine ⟨3246266504959157916481465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4328355339945543888641953 3246266504959157916481465)
        ·
          refine ⟨2434699878719368437361099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3246266504959157916481465 2434699878719368437361099)
          ·
            refine ⟨3652049818079052656041649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2434699878719368437361099 3652049818079052656041649)
            ·
              refine ⟨2739037363559289492031237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3652049818079052656041649 2739037363559289492031237)
              ·
                refine ⟨513569505667366779755857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2739037363559289492031237 513569505667366779755857)
                ·
                  refine ⟨385177129250525084816893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 513569505667366779755857 385177129250525084816893)
                  ·
                    refine ⟨144441423468946906806335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 385177129250525084816893 144441423468946906806335)
                    ·
                      rfl

theorem cell22_421948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_421948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_421948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_421948 prefixEnd_421948 := by exact prefixLift 421948
  have htrace : WordTrace (prefixWord ++ tailWord_421948) baseStart_421948 baseEnd_421948 := by
    simpa [prefixWord, tailWord_421948, baseEnd_421948] using wordTrace_append hprefix tailTrace_421948
  have hstable : (prefixWord ++ tailWord_421948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421948).length < 2 ^ (prefixWord ++ tailWord_421948).sum := by decide
  have hdescent : baseEnd_421948 < baseStart_421948 := by decide
  rcases family_descends (prefixWord ++ tailWord_421948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421950 : List Nat := [4, 2, 1, 3, 2, 2, 1, 1, 6]
def baseStart_421950 : Nat := 118140960795 + 421950 * 2 ^ 59
def prefixEnd_421950 : Nat := 4983230072969 + 3 ^ 40 * 421950 * 2
def baseEnd_421950 : Nat := 48147369369939856085443

theorem tailTrace_421950 : CollatzResearch.WordTrace tailWord_421950 prefixEnd_421950 48147369369939856085443 := by
  unfold tailWord_421950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1923722602669336020981913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10259853880903125445236869 1923722602669336020981913)
  ·
    refine ⟨1442791952002002015736435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1923722602669336020981913 1442791952002002015736435)
    ·
      refine ⟨2164187928003003023604653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1442791952002002015736435 2164187928003003023604653)
      ·
        refine ⟨811570473001126133851745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2164187928003003023604653 811570473001126133851745)
        ·
          refine ⟨608677854750844600388809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 811570473001126133851745 608677854750844600388809)
          ·
            refine ⟨456508391063133450291607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 608677854750844600388809 456508391063133450291607)
            ·
              refine ⟨684762586594700175437411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 456508391063133450291607 684762586594700175437411)
              ·
                refine ⟨1027143879892050263156117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 684762586594700175437411 1027143879892050263156117)
                ·
                  refine ⟨48147369369939856085443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1027143879892050263156117 48147369369939856085443)
                  ·
                    rfl

theorem cell22_421950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_421950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_421950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_421950 prefixEnd_421950 := by exact prefixLift 421950
  have htrace : WordTrace (prefixWord ++ tailWord_421950) baseStart_421950 baseEnd_421950 := by
    simpa [prefixWord, tailWord_421950, baseEnd_421950] using wordTrace_append hprefix tailTrace_421950
  have hstable : (prefixWord ++ tailWord_421950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421950).length < 2 ^ (prefixWord ++ tailWord_421950).sum := by decide
  have hdescent : baseEnd_421950 < baseStart_421950 := by decide
  rcases family_descends (prefixWord ++ tailWord_421950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421965 : List Nat := [1, 6, 1, 1, 1, 1, 3, 3, 2, 3]
def baseStart_421965 : Nat := 118140960795 + 421965 * 2 ^ 59
def prefixEnd_421965 : Nat := 4983230072969 + 3 ^ 40 * 421965 * 2
def baseEnd_421965 : Nat := 144447242916364529131283

theorem tailTrace_421965 : CollatzResearch.WordTrace tailWord_421965 prefixEnd_421965 144447242916364529131283 := by
  unfold tailWord_421965
  simp only [CollatzResearch.WordTrace]
  refine ⟨15390327916300345729651349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10260218610866897153100899 15390327916300345729651349)
  ·
    refine ⟨721421621076578706077407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15390327916300345729651349 721421621076578706077407)
    ·
      refine ⟨1082132431614868059116111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 721421621076578706077407 1082132431614868059116111)
      ·
        refine ⟨1623198647422302088674167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1082132431614868059116111 1623198647422302088674167)
        ·
          refine ⟨2434797971133453133011251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1623198647422302088674167 2434797971133453133011251)
          ·
            refine ⟨3652196956700179699516877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2434797971133453133011251 3652196956700179699516877)
            ·
              refine ⟨1369573858762567387318829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3652196956700179699516877 1369573858762567387318829)
              ·
                refine ⟨513590197035962770244561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1369573858762567387318829 513590197035962770244561)
                ·
                  refine ⟨385192647776972077683421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 513590197035962770244561 385192647776972077683421)
                  ·
                    refine ⟨144447242916364529131283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 385192647776972077683421 144447242916364529131283)
                    ·
                      rfl

theorem cell22_421965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_421965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_421965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_421965 prefixEnd_421965 := by exact prefixLift 421965
  have htrace : WordTrace (prefixWord ++ tailWord_421965) baseStart_421965 baseEnd_421965 := by
    simpa [prefixWord, tailWord_421965, baseEnd_421965] using wordTrace_append hprefix tailTrace_421965
  have hstable : (prefixWord ++ tailWord_421965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421965).length < 2 ^ (prefixWord ++ tailWord_421965).sum := by decide
  have hdescent : baseEnd_421965 < baseStart_421965 := by decide
  rcases family_descends (prefixWord ++ tailWord_421965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421982 : List Nat := [4, 4, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_421982 : Nat := 118140960795 + 421982 * 2 ^ 59
def prefixEnd_421982 : Nat := 4983230072969 + 3 ^ 40 * 421982 * 2
def baseEnd_421982 : Nat := 144453062363782151456231

theorem tailTrace_421982 : CollatzResearch.WordTrace tailWord_421982 prefixEnd_421982 144453062363782151456231 := by
  unfold tailWord_421982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1923868494654844704127525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10260631971492505088680133 1923868494654844704127525)
  ·
    refine ⟨360725342747783382023911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1923868494654844704127525 360725342747783382023911)
    ·
      refine ⟨541088014121675073035867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360725342747783382023911 541088014121675073035867)
      ·
        refine ⟨811632021182512609553801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541088014121675073035867 811632021182512609553801)
        ·
          refine ⟨608724015886884457165351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 811632021182512609553801 608724015886884457165351)
          ·
            refine ⟨913086023830326685748027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 608724015886884457165351 913086023830326685748027)
            ·
              refine ⟨1369629035745490028622041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913086023830326685748027 1369629035745490028622041)
              ·
                refine ⟨1027221776809117521466531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1369629035745490028622041 1027221776809117521466531)
                ·
                  refine ⟨1540832665213676282199797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1027221776809117521466531 1540832665213676282199797)
                  ·
                    refine ⟨144453062363782151456231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1540832665213676282199797 144453062363782151456231)
                    ·
                      rfl

theorem cell22_421982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_421982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_421982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_421982 prefixEnd_421982 := by exact prefixLift 421982
  have htrace : WordTrace (prefixWord ++ tailWord_421982) baseStart_421982 baseEnd_421982 := by
    simpa [prefixWord, tailWord_421982, baseEnd_421982] using wordTrace_append hprefix tailTrace_421982
  have hstable : (prefixWord ++ tailWord_421982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421982).length < 2 ^ (prefixWord ++ tailWord_421982).sum := by decide
  have hdescent : baseEnd_421982 < baseStart_421982 := by decide
  rcases family_descends (prefixWord ++ tailWord_421982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422021 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 1, 7]
def baseStart_422021 : Nat := 118140960795 + 422021 * 2 ^ 59
def prefixEnd_422021 : Nat := 4983230072969 + 3 ^ 40 * 422021 * 2
def baseEnd_422021 : Nat := 144466412860799049731111

theorem tailTrace_422021 : CollatzResearch.WordTrace tailWord_422021 prefixEnd_422021 144466412860799049731111 := by
  unfold tailWord_422021
  simp only [CollatzResearch.WordTrace]
  refine ⟨15392370404097467293689917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10261580269398311529126611 15392370404097467293689917)
  ·
    refine ⟨5772138901536550235133719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15392370404097467293689917 5772138901536550235133719)
    ·
      refine ⟨8658208352304825352700579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5772138901536550235133719 8658208352304825352700579)
      ·
        refine ⟨12987312528457238029050869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8658208352304825352700579 12987312528457238029050869)
        ·
          refine ⟨1217560549542866065223519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12987312528457238029050869 1217560549542866065223519)
          ·
            refine ⟨1826340824314299097835279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1217560549542866065223519 1826340824314299097835279)
            ·
              refine ⟨2739511236471448646752919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1826340824314299097835279 2739511236471448646752919)
              ·
                refine ⟨4109266854707172970129379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2739511236471448646752919 4109266854707172970129379)
                ·
                  refine ⟨6163900282060759455194069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4109266854707172970129379 6163900282060759455194069)
                  ·
                    refine ⟨144466412860799049731111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6163900282060759455194069 144466412860799049731111)
                    ·
                      rfl

theorem cell22_422021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_422021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_422021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_422021 prefixEnd_422021 := by exact prefixLift 422021
  have htrace : WordTrace (prefixWord ++ tailWord_422021) baseStart_422021 baseEnd_422021 := by
    simpa [prefixWord, tailWord_422021, baseEnd_422021] using wordTrace_append hprefix tailTrace_422021
  have hstable : (prefixWord ++ tailWord_422021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422021).length < 2 ^ (prefixWord ++ tailWord_422021).sum := by decide
  have hdescent : baseEnd_422021 < baseStart_422021 := by decide
  rcases family_descends (prefixWord ++ tailWord_422021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422053 : List Nat := [1, 3, 1, 2, 1, 3, 3, 3, 1, 4]
def baseStart_422053 : Nat := 118140960795 + 422053 * 2 ^ 59
def prefixEnd_422053 : Nat := 4983230072969 + 3 ^ 40 * 422053 * 2
def baseEnd_422053 : Nat := 144477367114761632931013

theorem tailTrace_422053 : CollatzResearch.WordTrace tailWord_422053 prefixEnd_422053 144477367114761632931013 := by
  unfold tailWord_422053
  simp only [CollatzResearch.WordTrace]
  refine ⟨15393537539981536758854813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10262358359987691172569875 15393537539981536758854813)
  ·
    refine ⟨5772576577493076284570555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15393537539981536758854813 5772576577493076284570555)
    ·
      refine ⟨8658864866239614426855833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5772576577493076284570555 8658864866239614426855833)
      ·
        refine ⟨6494148649679710820141875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8658864866239614426855833 6494148649679710820141875)
        ·
          refine ⟨9741222974519566230212813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6494148649679710820141875 9741222974519566230212813)
          ·
            refine ⟨3652958615444837336329805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9741222974519566230212813 3652958615444837336329805)
            ·
              refine ⟨1369859480791814001123677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3652958615444837336329805 1369859480791814001123677)
              ·
                refine ⟨513697305296930250421379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1369859480791814001123677 513697305296930250421379)
                ·
                  refine ⟨770545957945395375632069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 513697305296930250421379 770545957945395375632069)
                  ·
                    refine ⟨144477367114761632931013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 770545957945395375632069 144477367114761632931013)
                    ·
                      rfl

theorem cell22_422053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 4].length) (baseStart_422053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_422053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_422053 prefixEnd_422053 := by exact prefixLift 422053
  have htrace : WordTrace (prefixWord ++ tailWord_422053) baseStart_422053 baseEnd_422053 := by
    simpa [prefixWord, tailWord_422053, baseEnd_422053] using wordTrace_append hprefix tailTrace_422053
  have hstable : (prefixWord ++ tailWord_422053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422053).length < 2 ^ (prefixWord ++ tailWord_422053).sum := by decide
  have hdescent : baseEnd_422053 < baseStart_422053 := by decide
  rcases family_descends (prefixWord ++ tailWord_422053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422098 : List Nat := [3, 2, 2, 2, 1, 2, 2, 1, 1, 6]
def baseStart_422098 : Nat := 118140960795 + 422098 * 2 ^ 59
def prefixEnd_422098 : Nat := 4983230072969 + 3 ^ 40 * 422098 * 2
def baseEnd_422098 : Nat := 144492771534396515555875

theorem tailTrace_422098 : CollatzResearch.WordTrace tailWord_422098 prefixEnd_422098 144492771534396515555875 := by
  unfold tailWord_422098
  simp only [CollatzResearch.WordTrace]
  refine ⟨3848794706204627361060737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10263452549879006296161965 3848794706204627361060737)
  ·
    refine ⟨2886596029653470520795553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3848794706204627361060737 2886596029653470520795553)
    ·
      refine ⟨2164947022240102890596665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2886596029653470520795553 2164947022240102890596665)
      ·
        refine ⟨1623710266680077167947499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2164947022240102890596665 1623710266680077167947499)
        ·
          refine ⟨2435565400020115751921249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1623710266680077167947499 2435565400020115751921249)
          ·
            refine ⟨1826674050015086813940937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2435565400020115751921249 1826674050015086813940937)
            ·
              refine ⟨1370005537511315110455703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1826674050015086813940937 1370005537511315110455703)
              ·
                refine ⟨2055008306266972665683555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1370005537511315110455703 2055008306266972665683555)
                ·
                  refine ⟨3082512459400458998525333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2055008306266972665683555 3082512459400458998525333)
                  ·
                    refine ⟨144492771534396515555875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3082512459400458998525333 144492771534396515555875)
                    ·
                      rfl

theorem cell22_422098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_422098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_422098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_422098 prefixEnd_422098 := by exact prefixLift 422098
  have htrace : WordTrace (prefixWord ++ tailWord_422098) baseStart_422098 baseEnd_422098 := by
    simpa [prefixWord, tailWord_422098, baseEnd_422098] using wordTrace_append hprefix tailTrace_422098
  have hstable : (prefixWord ++ tailWord_422098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422098).length < 2 ^ (prefixWord ++ tailWord_422098).sum := by decide
  have hdescent : baseEnd_422098 < baseStart_422098 := by decide
  rcases family_descends (prefixWord ++ tailWord_422098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422175 : List Nat := [1, 1, 2, 4, 3, 2, 2, 2, 5]
def baseStart_422175 : Nat := 118140960795 + 422175 * 2 ^ 59
def prefixEnd_422175 : Nat := 4983230072969 + 3 ^ 40 * 422175 * 2
def baseEnd_422175 : Nat := 48173043402664660460213

theorem tailTrace_422175 : CollatzResearch.WordTrace tailWord_422175 prefixEnd_422175 48173043402664660460213 := by
  unfold tailWord_422175
  simp only [CollatzResearch.WordTrace]
  refine ⟨15397987245539551594795979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10265324830359701063197319 15397987245539551594795979)
  ·
    refine ⟨23096980868309327392193969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15397987245539551594795979 23096980868309327392193969)
    ·
      refine ⟨17322735651231995544145477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23096980868309327392193969 17322735651231995544145477)
      ·
        refine ⟨3248012934605999164527277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17322735651231995544145477 3248012934605999164527277)
        ·
          refine ⟨1218004850477249686697729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3248012934605999164527277 1218004850477249686697729)
          ·
            refine ⟨913503637857937265023297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1218004850477249686697729 913503637857937265023297)
            ·
              refine ⟨685127728393452948767473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 913503637857937265023297 685127728393452948767473)
              ·
                refine ⟨513845796295089711575605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 685127728393452948767473 513845796295089711575605)
                ·
                  refine ⟨48173043402664660460213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 513845796295089711575605 48173043402664660460213)
                  ·
                    rfl

theorem cell22_422175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 5].length) (baseStart_422175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_422175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_422175 prefixEnd_422175 := by exact prefixLift 422175
  have htrace : WordTrace (prefixWord ++ tailWord_422175) baseStart_422175 baseEnd_422175 := by
    simpa [prefixWord, tailWord_422175, baseEnd_422175] using wordTrace_append hprefix tailTrace_422175
  have hstable : (prefixWord ++ tailWord_422175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422175).length < 2 ^ (prefixWord ++ tailWord_422175).sum := by decide
  have hdescent : baseEnd_422175 < baseStart_422175 := by decide
  rcases family_descends (prefixWord ++ tailWord_422175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422188 : List Nat := [2, 2, 1, 1, 1, 3, 3, 2, 3, 4]
def baseStart_422188 : Nat := 118140960795 + 422188 * 2 ^ 59
def prefixEnd_422188 : Nat := 4983230072969 + 3 ^ 40 * 422188 * 2
def baseEnd_422188 : Nat := 144523580373666280805599

theorem tailTrace_422188 : CollatzResearch.WordTrace tailWord_422188 prefixEnd_422188 144523580373666280805599 := by
  unfold tailWord_422188
  simp only [CollatzResearch.WordTrace]
  refine ⟨7699230697246227407509609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10265640929661636543346145 7699230697246227407509609)
  ·
    refine ⟨5774423022934670555632207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7699230697246227407509609 5774423022934670555632207)
    ·
      refine ⟨8661634534402005833448311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5774423022934670555632207 8661634534402005833448311)
      ·
        refine ⟨12992451801603008750172467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8661634534402005833448311 12992451801603008750172467)
        ·
          refine ⟨19488677702404513125258701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12992451801603008750172467 19488677702404513125258701)
          ·
            refine ⟨7308254138401692421972013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19488677702404513125258701 7308254138401692421972013)
            ·
              refine ⟨2740595301900634658239505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7308254138401692421972013 2740595301900634658239505)
              ·
                refine ⟨2055446476425475993679629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2740595301900634658239505 2055446476425475993679629)
                ·
                  refine ⟨770792428659553497629861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2055446476425475993679629 770792428659553497629861)
                  ·
                    refine ⟨144523580373666280805599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 770792428659553497629861 144523580373666280805599)
                    ·
                      rfl

theorem cell22_422188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_422188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_422188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_422188 prefixEnd_422188 := by exact prefixLift 422188
  have htrace : WordTrace (prefixWord ++ tailWord_422188) baseStart_422188 baseEnd_422188 := by
    simpa [prefixWord, tailWord_422188, baseEnd_422188] using wordTrace_append hprefix tailTrace_422188
  have hstable : (prefixWord ++ tailWord_422188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422188).length < 2 ^ (prefixWord ++ tailWord_422188).sum := by decide
  have hdescent : baseEnd_422188 < baseStart_422188 := by decide
  rcases family_descends (prefixWord ++ tailWord_422188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422233 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 4, 4]
def baseStart_422233 : Nat := 118140960795 + 422233 * 2 ^ 59
def prefixEnd_422233 : Nat := 4983230072969 + 3 ^ 40 * 422233 * 2
def baseEnd_422233 : Nat := 144538984793301163430461

theorem tailTrace_422233 : CollatzResearch.WordTrace tailWord_422233 prefixEnd_422233 144538984793301163430461 := by
  unfold tailWord_422233
  simp only [CollatzResearch.WordTrace]
  refine ⟨15400102679329427500407353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10266735119552951666938235 15400102679329427500407353)
  ·
    refine ⟨11550077009497070625305515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15400102679329427500407353 11550077009497070625305515)
    ·
      refine ⟨17325115514245605937958273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11550077009497070625305515 17325115514245605937958273)
      ·
        refine ⟨12993836635684204453468705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17325115514245605937958273 12993836635684204453468705)
        ·
          refine ⟨9745377476763153340101529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12993836635684204453468705 9745377476763153340101529)
          ·
            refine ⟨7309033107572365005076147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9745377476763153340101529 7309033107572365005076147)
            ·
              refine ⟨10963549661358547507614221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7309033107572365005076147 10963549661358547507614221)
              ·
                refine ⟨4111331123009455315355333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10963549661358547507614221 4111331123009455315355333)
                ·
                  refine ⟨770874585564272871629125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4111331123009455315355333 770874585564272871629125)
                  ·
                    refine ⟨144538984793301163430461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 770874585564272871629125 144538984793301163430461)
                    ·
                      rfl

theorem cell22_422233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 4].length) (baseStart_422233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_422233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_422233 prefixEnd_422233 := by exact prefixLift 422233
  have htrace : WordTrace (prefixWord ++ tailWord_422233) baseStart_422233 baseEnd_422233 := by
    simpa [prefixWord, tailWord_422233, baseEnd_422233] using wordTrace_append hprefix tailTrace_422233
  have hstable : (prefixWord ++ tailWord_422233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422233).length < 2 ^ (prefixWord ++ tailWord_422233).sum := by decide
  have hdescent : baseEnd_422233 < baseStart_422233 := by decide
  rcases family_descends (prefixWord ++ tailWord_422233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422250 : List Nat := [3, 1, 3, 3, 1, 1, 1, 2, 1, 6]
def baseStart_422250 : Nat := 118140960795 + 422250 * 2 ^ 59
def prefixEnd_422250 : Nat := 4983230072969 + 3 ^ 40 * 422250 * 2
def baseEnd_422250 : Nat := 144544804240718785755409

theorem tailTrace_422250 : CollatzResearch.WordTrace tailWord_422250 prefixEnd_422250 144544804240718785755409 := by
  unfold tailWord_422250
  simp only [CollatzResearch.WordTrace]
  refine ⟨3850180680066959850944051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10267148480178559602517469 3850180680066959850944051)
  ·
    refine ⟨5775271020100439776416077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3850180680066959850944051 5775271020100439776416077)
    ·
      refine ⟨2165726632537664916156029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5775271020100439776416077 2165726632537664916156029)
      ·
        refine ⟨812147487201624343558511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2165726632537664916156029 812147487201624343558511)
        ·
          refine ⟨1218221230802436515337767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 812147487201624343558511 1218221230802436515337767)
          ·
            refine ⟨1827331846203654773006651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1218221230802436515337767 1827331846203654773006651)
            ·
              refine ⟨2740997769305482159509977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1827331846203654773006651 2740997769305482159509977)
              ·
                refine ⟨2055748326979111619632483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2740997769305482159509977 2055748326979111619632483)
                ·
                  refine ⟨3083622490468667429448725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2055748326979111619632483 3083622490468667429448725)
                  ·
                    refine ⟨144544804240718785755409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3083622490468667429448725 144544804240718785755409)
                    ·
                      rfl

theorem cell22_422250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_422250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_422250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_422250 prefixEnd_422250 := by exact prefixLift 422250
  have htrace : WordTrace (prefixWord ++ tailWord_422250) baseStart_422250 baseEnd_422250 := by
    simpa [prefixWord, tailWord_422250, baseEnd_422250] using wordTrace_append hprefix tailTrace_422250
  have hstable : (prefixWord ++ tailWord_422250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422250).length < 2 ^ (prefixWord ++ tailWord_422250).sum := by decide
  have hdescent : baseEnd_422250 < baseStart_422250 := by decide
  rcases family_descends (prefixWord ++ tailWord_422250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422252 : List Nat := [2, 2, 1, 1, 6, 2, 1, 1, 1, 5]
def baseStart_422252 : Nat := 118140960795 + 422252 * 2 ^ 59
def prefixEnd_422252 : Nat := 4983230072969 + 3 ^ 40 * 422252 * 2
def baseEnd_422252 : Nat := 144545488881591447205403

theorem tailTrace_422252 : CollatzResearch.WordTrace tailWord_422252 prefixEnd_422252 144545488881591447205403 := by
  unfold tailWord_422252
  simp only [CollatzResearch.WordTrace]
  refine ⟨7700397833130296872674505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10267197110840395830232673 7700397833130296872674505)
  ·
    refine ⟨5775298374847722654505879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7700397833130296872674505 5775298374847722654505879)
    ·
      refine ⟨8662947562271583981758819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5775298374847722654505879 8662947562271583981758819)
      ·
        refine ⟨12994421343407375972638229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8662947562271583981758819 12994421343407375972638229)
        ·
          refine ⟨609113500472220748717417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12994421343407375972638229 609113500472220748717417)
          ·
            refine ⟨456835125354165561538063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 609113500472220748717417 456835125354165561538063)
            ·
              refine ⟨685252688031248342307095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 456835125354165561538063 685252688031248342307095)
              ·
                refine ⟨1027879032046872513460643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 685252688031248342307095 1027879032046872513460643)
                ·
                  refine ⟨1541818548070308770190965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1027879032046872513460643 1541818548070308770190965)
                  ·
                    refine ⟨144545488881591447205403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1541818548070308770190965 144545488881591447205403)
                    ·
                      rfl

theorem cell22_422252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 5].length) (baseStart_422252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_422252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_422252 prefixEnd_422252 := by exact prefixLift 422252
  have htrace : WordTrace (prefixWord ++ tailWord_422252) baseStart_422252 baseEnd_422252 := by
    simpa [prefixWord, tailWord_422252, baseEnd_422252] using wordTrace_append hprefix tailTrace_422252
  have hstable : (prefixWord ++ tailWord_422252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422252).length < 2 ^ (prefixWord ++ tailWord_422252).sum := by decide
  have hdescent : baseEnd_422252 < baseStart_422252 := by decide
  rcases family_descends (prefixWord ++ tailWord_422252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422282 : List Nat := [3, 1, 2, 5, 1, 2, 8]
def baseStart_422282 : Nat := 118140960795 + 422282 * 2 ^ 59
def prefixEnd_422282 : Nat := 4983230072969 + 3 ^ 40 * 422282 * 2
def baseEnd_422282 : Nat := 5353916981284495146493

theorem tailTrace_422282 : CollatzResearch.WordTrace tailWord_422282 prefixEnd_422282 5353916981284495146493 := by
  unfold tailWord_422282
  simp only [CollatzResearch.WordTrace]
  refine ⟨3850472464037977217235275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10267926570767939245960733 3850472464037977217235275)
  ·
    refine ⟨5775708696056965825852913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3850472464037977217235275 5775708696056965825852913)
    ·
      refine ⟨4331781522042724369389685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5775708696056965825852913 4331781522042724369389685)
      ·
        refine ⟨406104517691505409630283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4331781522042724369389685 406104517691505409630283)
        ·
          refine ⟨609156776537258114445425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406104517691505409630283 609156776537258114445425)
          ·
            refine ⟨456867582402943585834069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 609156776537258114445425 456867582402943585834069)
            ·
              refine ⟨5353916981284495146493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 456867582402943585834069 5353916981284495146493)
              ·
                rfl

theorem cell22_422282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 8].length) (baseStart_422282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_422282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_422282 prefixEnd_422282 := by exact prefixLift 422282
  have htrace : WordTrace (prefixWord ++ tailWord_422282) baseStart_422282 baseEnd_422282 := by
    simpa [prefixWord, tailWord_422282, baseEnd_422282] using wordTrace_append hprefix tailTrace_422282
  have hstable : (prefixWord ++ tailWord_422282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422282).length < 2 ^ (prefixWord ++ tailWord_422282).sum := by decide
  have hdescent : baseEnd_422282 < baseStart_422282 := by decide
  rcases family_descends (prefixWord ++ tailWord_422282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422348 : List Nat := [2, 2, 1, 4, 3, 2, 2, 2, 1, 3]
def baseStart_422348 : Nat := 118140960795 + 422348 * 2 ^ 59
def prefixEnd_422348 : Nat := 4983230072969 + 3 ^ 40 * 422348 * 2
def baseEnd_422348 : Nat := 144578351643479196805109

theorem tailTrace_422348 : CollatzResearch.WordTrace tailWord_422348 prefixEnd_422348 144578351643479196805109 := by
  unfold tailWord_422348
  simp only [CollatzResearch.WordTrace]
  refine ⟨7702148536956401070421849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10269531382608534760562465 7702148536956401070421849)
  ·
    refine ⟨5776611402717300802816387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7702148536956401070421849 5776611402717300802816387)
    ·
      refine ⟨8664917104075951204224581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5776611402717300802816387 8664917104075951204224581)
      ·
        refine ⟨1624671957014240850792109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8664917104075951204224581 1624671957014240850792109)
        ·
          refine ⟨609251983880340319047041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1624671957014240850792109 609251983880340319047041)
          ·
            refine ⟨456938987910255239285281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 609251983880340319047041 456938987910255239285281)
            ·
              refine ⟨342704240932691429463961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 456938987910255239285281 342704240932691429463961)
              ·
                refine ⟨257028180699518572097971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 342704240932691429463961 257028180699518572097971)
                ·
                  refine ⟨385542271049277858146957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 257028180699518572097971 385542271049277858146957)
                  ·
                    refine ⟨144578351643479196805109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 385542271049277858146957 144578351643479196805109)
                    ·
                      rfl

theorem cell22_422348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 2, 1, 3].length) (baseStart_422348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_422348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_422348 prefixEnd_422348 := by exact prefixLift 422348
  have htrace : WordTrace (prefixWord ++ tailWord_422348) baseStart_422348 baseEnd_422348 := by
    simpa [prefixWord, tailWord_422348, baseEnd_422348] using wordTrace_append hprefix tailTrace_422348
  have hstable : (prefixWord ++ tailWord_422348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422348).length < 2 ^ (prefixWord ++ tailWord_422348).sum := by decide
  have hdescent : baseEnd_422348 < baseStart_422348 := by decide
  rcases family_descends (prefixWord ++ tailWord_422348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422385 : List Nat := [1, 2, 2, 2, 3, 1, 3, 1, 1, 6]
def baseStart_422385 : Nat := 118140960795 + 422385 * 2 ^ 59
def prefixEnd_422385 : Nat := 4983230072969 + 3 ^ 40 * 422385 * 2
def baseEnd_422385 : Nat := 144591017499623433629995

theorem tailTrace_422385 : CollatzResearch.WordTrace tailWord_422385 prefixEnd_422385 144591017499623433629995 := by
  unfold tailWord_422385
  simp only [CollatzResearch.WordTrace]
  refine ⟨15405646574778757459940609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10270431049852504973293739 15405646574778757459940609)
  ·
    refine ⟨11554234931084068094955457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15405646574778757459940609 11554234931084068094955457)
    ·
      refine ⟨8665676198313051071216593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11554234931084068094955457 8665676198313051071216593)
      ·
        refine ⟨6499257148734788303412445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8665676198313051071216593 6499257148734788303412445)
        ·
          refine ⟨2437221430775545613779667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6499257148734788303412445 2437221430775545613779667)
          ·
            refine ⟨3655832146163318420669501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2437221430775545613779667 3655832146163318420669501)
            ·
              refine ⟨1370937054811244407751063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3655832146163318420669501 1370937054811244407751063)
              ·
                refine ⟨2056405582216866611626595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1370937054811244407751063 2056405582216866611626595)
                ·
                  refine ⟨3084608373325299917439893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2056405582216866611626595 3084608373325299917439893)
                  ·
                    refine ⟨144591017499623433629995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3084608373325299917439893 144591017499623433629995)
                    ·
                      rfl

theorem cell22_422385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_422385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_422385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_422385 prefixEnd_422385 := by exact prefixLift 422385
  have htrace : WordTrace (prefixWord ++ tailWord_422385) baseStart_422385 baseEnd_422385 := by
    simpa [prefixWord, tailWord_422385, baseEnd_422385] using wordTrace_append hprefix tailTrace_422385
  have hstable : (prefixWord ++ tailWord_422385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422385).length < 2 ^ (prefixWord ++ tailWord_422385).sum := by decide
  have hdescent : baseEnd_422385 < baseStart_422385 := by decide
  rcases family_descends (prefixWord ++ tailWord_422385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422404 : List Nat := [2, 3, 2, 3, 1, 2, 1, 1, 4, 3]
def baseStart_422404 : Nat := 118140960795 + 422404 * 2 ^ 59
def prefixEnd_422404 : Nat := 4983230072969 + 3 ^ 40 * 422404 * 2
def baseEnd_422404 : Nat := 144597521587913717404937

theorem tailTrace_422404 : CollatzResearch.WordTrace tailWord_422404 prefixEnd_422404 144597521587913717404937 := by
  unfold tailWord_422404
  simp only [CollatzResearch.WordTrace]
  refine ⟨7703169780854961852441133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10270893041139949136588177 7703169780854961852441133)
  ·
    refine ⟨2888688667820610694665425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7703169780854961852441133 2888688667820610694665425)
    ·
      refine ⟨2166516500865458020999069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2888688667820610694665425 2166516500865458020999069)
      ·
        refine ⟨812443687824546757874651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2166516500865458020999069 812443687824546757874651)
        ·
          refine ⟨1218665531736820136811977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 812443687824546757874651 1218665531736820136811977)
          ·
            refine ⟨913999148802615102608983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1218665531736820136811977 913999148802615102608983)
            ·
              refine ⟨1370998723203922653913475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913999148802615102608983 1370998723203922653913475)
              ·
                refine ⟨2056498084805883980870213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1370998723203922653913475 2056498084805883980870213)
                ·
                  refine ⟨385593390901103246413165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2056498084805883980870213 385593390901103246413165)
                  ·
                    refine ⟨144597521587913717404937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 385593390901103246413165 144597521587913717404937)
                    ·
                      rfl

theorem cell22_422404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_422404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_422404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_422404 prefixEnd_422404 := by exact prefixLift 422404
  have htrace : WordTrace (prefixWord ++ tailWord_422404) baseStart_422404 baseEnd_422404 := by
    simpa [prefixWord, tailWord_422404, baseEnd_422404] using wordTrace_append hprefix tailTrace_422404
  have hstable : (prefixWord ++ tailWord_422404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422404).length < 2 ^ (prefixWord ++ tailWord_422404).sum := by decide
  have hdescent : baseEnd_422404 < baseStart_422404 := by decide
  rcases family_descends (prefixWord ++ tailWord_422404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422406 : List Nat := [6, 2, 1, 1, 1, 1, 1, 3, 6]
def baseStart_422406 : Nat := 118140960795 + 422406 * 2 ^ 59
def prefixEnd_422406 : Nat := 4983230072969 + 3 ^ 40 * 422406 * 2
def baseEnd_422406 : Nat := 48199402076262126284977

theorem tailTrace_422406 : CollatzResearch.WordTrace tailWord_422406 prefixEnd_422406 48199402076262126284977 := by
  unfold tailWord_422406
  simp only [CollatzResearch.WordTrace]
  refine ⟨481450390865708688951721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10270941671801785364303381 481450390865708688951721)
  ·
    refine ⟨361087793149281516713791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 481450390865708688951721 361087793149281516713791)
    ·
      refine ⟨541631689723922275070687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361087793149281516713791 541631689723922275070687)
      ·
        refine ⟨812447534585883412606031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541631689723922275070687 812447534585883412606031)
        ·
          refine ⟨1218671301878825118909047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 812447534585883412606031 1218671301878825118909047)
          ·
            refine ⟨1828006952818237678363571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1218671301878825118909047 1828006952818237678363571)
            ·
              refine ⟨2742010429227356517545357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1828006952818237678363571 2742010429227356517545357)
              ·
                refine ⟨1028253910960258694079509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2742010429227356517545357 1028253910960258694079509)
                ·
                  refine ⟨48199402076262126284977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1028253910960258694079509 48199402076262126284977)
                  ·
                    rfl

theorem cell22_422406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_422406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_422406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_422406 prefixEnd_422406 := by exact prefixLift 422406
  have htrace : WordTrace (prefixWord ++ tailWord_422406) baseStart_422406 baseEnd_422406 := by
    simpa [prefixWord, tailWord_422406, baseEnd_422406] using wordTrace_append hprefix tailTrace_422406
  have hstable : (prefixWord ++ tailWord_422406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422406).length < 2 ^ (prefixWord ++ tailWord_422406).sum := by decide
  have hdescent : baseEnd_422406 < baseStart_422406 := by decide
  rcases family_descends (prefixWord ++ tailWord_422406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422517 : List Nat := [1, 3, 4, 2, 3, 1, 2, 2, 1, 3]
def baseStart_422517 : Nat := 118140960795 + 422517 * 2 ^ 59
def prefixEnd_422517 : Nat := 4983230072969 + 3 ^ 40 * 422517 * 2
def baseEnd_422517 : Nat := 144636203797219089329591

theorem tailTrace_422517 : CollatzResearch.WordTrace tailWord_422517 prefixEnd_422517 144636203797219089329591 := by
  unfold tailWord_422517
  simp only [CollatzResearch.WordTrace]
  refine ⟨15410461010300544003745805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10273640673533696002497203 15410461010300544003745805)
  ·
    refine ⟨5778922878862704001404677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15410461010300544003745805 5778922878862704001404677)
    ·
      refine ⟨1083548039786757000263377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5778922878862704001404677 1083548039786757000263377)
      ·
        refine ⟨812661029840067750197533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1083548039786757000263377 812661029840067750197533)
        ·
          refine ⟨304747886190025406324075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 812661029840067750197533 304747886190025406324075)
          ·
            refine ⟨457121829285038109486113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304747886190025406324075 457121829285038109486113)
            ·
              refine ⟨342841371963778582114585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 457121829285038109486113 342841371963778582114585)
              ·
                refine ⟨257131028972833936585939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 342841371963778582114585 257131028972833936585939)
                ·
                  refine ⟨385696543459250904878909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 257131028972833936585939 385696543459250904878909)
                  ·
                    refine ⟨144636203797219089329591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 385696543459250904878909 144636203797219089329591)
                    ·
                      rfl

theorem cell22_422517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_422517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_422517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_422517 prefixEnd_422517 := by exact prefixLift 422517
  have htrace : WordTrace (prefixWord ++ tailWord_422517) baseStart_422517 baseEnd_422517 := by
    simpa [prefixWord, tailWord_422517, baseEnd_422517] using wordTrace_append hprefix tailTrace_422517
  have hstable : (prefixWord ++ tailWord_422517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422517).length < 2 ^ (prefixWord ++ tailWord_422517).sum := by decide
  have hdescent : baseEnd_422517 < baseStart_422517 := by decide
  rcases family_descends (prefixWord ++ tailWord_422517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422522 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 8, 3]
def baseStart_422522 : Nat := 118140960795 + 422522 * 2 ^ 59
def prefixEnd_422522 : Nat := 4983230072969 + 3 ^ 40 * 422522 * 2
def baseEnd_422522 : Nat := 144637915399400742954575

theorem tailTrace_422522 : CollatzResearch.WordTrace tailWord_422522 prefixEnd_422522 144637915399400742954575 := by
  unfold tailWord_422522
  simp only [CollatzResearch.WordTrace]
  refine ⟨3852660843820607464419455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10273762250188286571785213 3852660843820607464419455)
  ·
    refine ⟨5778991265730911196629183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3852660843820607464419455 5778991265730911196629183)
    ·
      refine ⟨8668486898596366794943775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5778991265730911196629183 8668486898596366794943775)
      ·
        refine ⟨13002730347894550192415663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8668486898596366794943775 13002730347894550192415663)
        ·
          refine ⟨19504095521841825288623495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13002730347894550192415663 19504095521841825288623495)
          ·
            refine ⟨29256143282762737932935243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19504095521841825288623495 29256143282762737932935243)
            ·
              refine ⟨43884214924144106899402865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29256143282762737932935243 43884214924144106899402865)
              ·
                refine ⟨32913161193108080174552149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43884214924144106899402865 32913161193108080174552149)
                ·
                  refine ⟨385701107731735314545533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32913161193108080174552149 385701107731735314545533)
                  ·
                    refine ⟨144637915399400742954575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 385701107731735314545533 144637915399400742954575)
                    ·
                      rfl

theorem cell22_422522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 8, 3].length) (baseStart_422522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_422522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_422522 prefixEnd_422522 := by exact prefixLift 422522
  have htrace : WordTrace (prefixWord ++ tailWord_422522) baseStart_422522 baseEnd_422522 := by
    simpa [prefixWord, tailWord_422522, baseEnd_422522] using wordTrace_append hprefix tailTrace_422522
  have hstable : (prefixWord ++ tailWord_422522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422522).length < 2 ^ (prefixWord ++ tailWord_422522).sum := by decide
  have hdescent : baseEnd_422522 < baseStart_422522 := by decide
  rcases family_descends (prefixWord ++ tailWord_422522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422573 : List Nat := [1, 5, 2, 1, 1, 4, 1, 2, 2, 3]
def baseStart_422573 : Nat := 118140960795 + 422573 * 2 ^ 59
def prefixEnd_422573 : Nat := 4983230072969 + 3 ^ 40 * 422573 * 2
def baseEnd_422573 : Nat := 144655373741653609929419

theorem tailTrace_422573 : CollatzResearch.WordTrace tailWord_422573 prefixEnd_422573 144655373741653609929419 := by
  unfold tailWord_422573
  simp only [CollatzResearch.WordTrace]
  refine ⟨15412503498097665567784373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10275002332065110378522915 15412503498097665567784373)
  ·
    refine ⟨1444922202946656146979785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15412503498097665567784373 1444922202946656146979785)
    ·
      refine ⟨1083691652209992110234839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1444922202946656146979785 1083691652209992110234839)
      ·
        refine ⟨1625537478314988165352259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1083691652209992110234839 1625537478314988165352259)
        ·
          refine ⟨2438306217472482248028389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1625537478314988165352259 2438306217472482248028389)
          ·
            refine ⟨457182415776090421505323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2438306217472482248028389 457182415776090421505323)
            ·
              refine ⟨685773623664135632257985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457182415776090421505323 685773623664135632257985)
              ·
                refine ⟨514330217748101724193489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 685773623664135632257985 514330217748101724193489)
                ·
                  refine ⟨385747663311076293145117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 514330217748101724193489 385747663311076293145117)
                  ·
                    refine ⟨144655373741653609929419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 385747663311076293145117 144655373741653609929419)
                    ·
                      rfl

theorem cell22_422573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_422573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_422573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_422573 prefixEnd_422573 := by exact prefixLift 422573
  have htrace : WordTrace (prefixWord ++ tailWord_422573) baseStart_422573 baseEnd_422573 := by
    simpa [prefixWord, tailWord_422573, baseEnd_422573] using wordTrace_append hprefix tailTrace_422573
  have hstable : (prefixWord ++ tailWord_422573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422573).length < 2 ^ (prefixWord ++ tailWord_422573).sum := by decide
  have hdescent : baseEnd_422573 < baseStart_422573 := by decide
  rcases family_descends (prefixWord ++ tailWord_422573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422687 : List Nat := [1, 1, 2, 4, 2, 12]
def baseStart_422687 : Nat := 118140960795 + 422687 * 2 ^ 59
def prefixEnd_422687 : Nat := 4983230072969 + 3 ^ 40 * 422687 * 2
def baseEnd_422687 : Nat := 1786350595943152007149

theorem tailTrace_422687 : CollatzResearch.WordTrace tailWord_422687 prefixEnd_422687 1786350595943152007149 := by
  unfold tailWord_422687
  simp only [CollatzResearch.WordTrace]
  refine ⟨15416661419684663037434315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10277774279789775358289543 15416661419684663037434315)
  ·
    refine ⟨23124992129526994556151473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15416661419684663037434315 23124992129526994556151473)
    ·
      refine ⟨17343744097145245917113605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23124992129526994556151473 17343744097145245917113605)
      ·
        refine ⟨3251952018214733609458801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17343744097145245917113605 3251952018214733609458801)
        ·
          refine ⟨2438964013661050207094101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3251952018214733609458801 2438964013661050207094101)
          ·
            refine ⟨1786350595943152007149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 2438964013661050207094101 1786350595943152007149)
            ·
              rfl

theorem cell22_422687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 12].length) (baseStart_422687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_422687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_422687 prefixEnd_422687 := by exact prefixLift 422687
  have htrace : WordTrace (prefixWord ++ tailWord_422687) baseStart_422687 baseEnd_422687 := by
    simpa [prefixWord, tailWord_422687, baseEnd_422687] using wordTrace_append hprefix tailTrace_422687
  have hstable : (prefixWord ++ tailWord_422687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422687).length < 2 ^ (prefixWord ++ tailWord_422687).sum := by decide
  have hdescent : baseEnd_422687 < baseStart_422687 := by decide
  rcases family_descends (prefixWord ++ tailWord_422687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422689 : List Nat := [1, 2, 3, 2, 1, 2, 1, 4, 2, 4]
def baseStart_422689 : Nat := 118140960795 + 422689 * 2 ^ 59
def prefixEnd_422689 : Nat := 4983230072969 + 3 ^ 40 * 422689 * 2
def baseEnd_422689 : Nat := 144695082912267974029063

theorem tailTrace_422689 : CollatzResearch.WordTrace tailWord_422689 prefixEnd_422689 144695082912267974029063 := by
  unfold tailWord_422689
  simp only [CollatzResearch.WordTrace]
  refine ⟨15416734365677417379007121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10277822910451611586004747 15416734365677417379007121)
  ·
    refine ⟨11562550774258063034255341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15416734365677417379007121 11562550774258063034255341)
    ·
      refine ⟨4335956540346773637845753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11562550774258063034255341 4335956540346773637845753)
      ·
        refine ⟨3251967405260080228384315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4335956540346773637845753 3251967405260080228384315)
        ·
          refine ⟨4877951107890120342576473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3251967405260080228384315 4877951107890120342576473)
          ·
            refine ⟨3658463330917590256932355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4877951107890120342576473 3658463330917590256932355)
            ·
              refine ⟨5487694996376385385398533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3658463330917590256932355 5487694996376385385398533)
              ·
                refine ⟨1028942811820572259762225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5487694996376385385398533 1028942811820572259762225)
                ·
                  refine ⟨771707108865429194821669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1028942811820572259762225 771707108865429194821669)
                  ·
                    refine ⟨144695082912267974029063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 771707108865429194821669 144695082912267974029063)
                    ·
                      rfl

theorem cell22_422689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_422689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_422689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_422689 prefixEnd_422689 := by exact prefixLift 422689
  have htrace : WordTrace (prefixWord ++ tailWord_422689) baseStart_422689 baseEnd_422689 := by
    simpa [prefixWord, tailWord_422689, baseEnd_422689] using wordTrace_append hprefix tailTrace_422689
  have hstable : (prefixWord ++ tailWord_422689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422689).length < 2 ^ (prefixWord ++ tailWord_422689).sum := by decide
  have hdescent : baseEnd_422689 < baseStart_422689 := by decide
  rcases family_descends (prefixWord ++ tailWord_422689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422708 : List Nat := [2, 5, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_422708 : Nat := 118140960795 + 422708 * 2 ^ 59
def prefixEnd_422708 : Nat := 4983230072969 + 3 ^ 40 * 422708 * 2
def baseEnd_422708 : Nat := 144701587000558257804005

theorem tailTrace_422708 : CollatzResearch.WordTrace tailWord_422708 prefixEnd_422708 144701587000558257804005 := by
  unfold tailWord_422708
  simp only [CollatzResearch.WordTrace]
  refine ⟨7708713676304291811974389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10278284901739055749299185 7708713676304291811974389)
  ·
    refine ⟨722691907153527357372599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7708713676304291811974389 722691907153527357372599)
    ·
      refine ⟨1084037860730291036058899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 722691907153527357372599 1084037860730291036058899)
      ·
        refine ⟨1626056791095436554088349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1084037860730291036058899 1626056791095436554088349)
        ·
          refine ⟨609771296660788707783131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1626056791095436554088349 609771296660788707783131)
          ·
            refine ⟨914656944991183061674697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609771296660788707783131 914656944991183061674697)
            ·
              refine ⟨685992708743387296256023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 914656944991183061674697 685992708743387296256023)
              ·
                refine ⟨1028989063115080944384035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 685992708743387296256023 1028989063115080944384035)
                ·
                  refine ⟨1543483594672621416576053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1028989063115080944384035 1543483594672621416576053)
                  ·
                    refine ⟨144701587000558257804005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1543483594672621416576053 144701587000558257804005)
                    ·
                      rfl

theorem cell22_422708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_422708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_422708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_422708 prefixEnd_422708 := by exact prefixLift 422708
  have htrace : WordTrace (prefixWord ++ tailWord_422708) baseStart_422708 baseEnd_422708 := by
    simpa [prefixWord, tailWord_422708, baseEnd_422708] using wordTrace_append hprefix tailTrace_422708
  have hstable : (prefixWord ++ tailWord_422708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422708).length < 2 ^ (prefixWord ++ tailWord_422708).sum := by decide
  have hdescent : baseEnd_422708 < baseStart_422708 := by decide
  rcases family_descends (prefixWord ++ tailWord_422708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422764 : List Nat := [2, 2, 1, 1, 4, 1, 1, 3, 2, 5]
def baseStart_422764 : Nat := 118140960795 + 422764 * 2 ^ 59
def prefixEnd_422764 : Nat := 4983230072969 + 3 ^ 40 * 422764 * 2
def baseEnd_422764 : Nat := 144720756944992778403833

theorem tailTrace_422764 : CollatzResearch.WordTrace tailWord_422764 prefixEnd_422764 144720756944992778403833 := by
  unfold tailWord_422764
  simp only [CollatzResearch.WordTrace]
  refine ⟨7709734920202852593993673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10279646560270470125324897 7709734920202852593993673)
  ·
    refine ⟨5782301190152139445495255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7709734920202852593993673 5782301190152139445495255)
    ·
      refine ⟨8673451785228209168242883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5782301190152139445495255 8673451785228209168242883)
      ·
        refine ⟨13010177677842313752364325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8673451785228209168242883 13010177677842313752364325)
        ·
          refine ⟨2439408314595433828568311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13010177677842313752364325 2439408314595433828568311)
          ·
            refine ⟨3659112471893150742852467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2439408314595433828568311 3659112471893150742852467)
            ·
              refine ⟨5488668707839726114278701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3659112471893150742852467 5488668707839726114278701)
              ·
                refine ⟨2058250765439897292854513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5488668707839726114278701 2058250765439897292854513)
                ·
                  refine ⟨1543688074079922969640885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2058250765439897292854513 1543688074079922969640885)
                  ·
                    refine ⟨144720756944992778403833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1543688074079922969640885 144720756944992778403833)
                    ·
                      rfl

theorem cell22_422764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_422764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_422764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_422764 prefixEnd_422764 := by exact prefixLift 422764
  have htrace : WordTrace (prefixWord ++ tailWord_422764) baseStart_422764 baseEnd_422764 := by
    simpa [prefixWord, tailWord_422764, baseEnd_422764] using wordTrace_append hprefix tailTrace_422764
  have hstable : (prefixWord ++ tailWord_422764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422764).length < 2 ^ (prefixWord ++ tailWord_422764).sum := by decide
  have hdescent : baseEnd_422764 < baseStart_422764 := by decide
  rcases family_descends (prefixWord ++ tailWord_422764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422779 : List Nat := [1, 1, 1, 1, 1, 5, 2, 3, 3, 4]
def baseStart_422779 : Nat := 118140960795 + 422779 * 2 ^ 59
def prefixEnd_422779 : Nat := 4983230072969 + 3 ^ 40 * 422779 * 2
def baseEnd_422779 : Nat := 144725891751537739278787

theorem tailTrace_422779 : CollatzResearch.WordTrace tailWord_422779 prefixEnd_422779 144725891751537739278787 := by
  unfold tailWord_422779
  simp only [CollatzResearch.WordTrace]
  refine ⟨15420016935351362749783391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10280011290234241833188927 15420016935351362749783391)
  ·
    refine ⟨23130025403027044124675087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15420016935351362749783391 23130025403027044124675087)
    ·
      refine ⟨34695038104540566187012631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23130025403027044124675087 34695038104540566187012631)
      ·
        refine ⟨52042557156810849280518947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34695038104540566187012631 52042557156810849280518947)
        ·
          refine ⟨78063835735216273920778421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52042557156810849280518947 78063835735216273920778421)
          ·
            refine ⟨7318484600176525680072977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78063835735216273920778421 7318484600176525680072977)
            ·
              refine ⟨5488863450132394260054733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7318484600176525680072977 5488863450132394260054733)
              ·
                refine ⟨2058323793799647847520525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5488863450132394260054733 2058323793799647847520525)
                ·
                  refine ⟨771871422674867942820197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2058323793799647847520525 771871422674867942820197)
                  ·
                    refine ⟨144725891751537739278787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 771871422674867942820197 144725891751537739278787)
                    ·
                      rfl

theorem cell22_422779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 4].length) (baseStart_422779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_422779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_422779 prefixEnd_422779 := by exact prefixLift 422779
  have htrace : WordTrace (prefixWord ++ tailWord_422779) baseStart_422779 baseEnd_422779 := by
    simpa [prefixWord, tailWord_422779, baseEnd_422779] using wordTrace_append hprefix tailTrace_422779
  have hstable : (prefixWord ++ tailWord_422779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422779).length < 2 ^ (prefixWord ++ tailWord_422779).sum := by decide
  have hdescent : baseEnd_422779 < baseStart_422779 := by decide
  rcases family_descends (prefixWord ++ tailWord_422779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422796 : List Nat := [2, 2, 1, 2, 1, 2, 4, 3, 1, 4]
def baseStart_422796 : Nat := 118140960795 + 422796 * 2 ^ 59
def prefixEnd_422796 : Nat := 4983230072969 + 3 ^ 40 * 422796 * 2
def baseEnd_422796 : Nat := 144731711198955361603735

theorem tailTrace_422796 : CollatzResearch.WordTrace tailWord_422796 prefixEnd_422796 144731711198955361603735 := by
  unfold tailWord_422796
  simp only [CollatzResearch.WordTrace]
  refine ⟨7710318488144887326576121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10280424650859849768768161 7710318488144887326576121)
  ·
    refine ⟨5782738866108665494932091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7710318488144887326576121 5782738866108665494932091)
    ·
      refine ⟨8674108299162998242398137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5782738866108665494932091 8674108299162998242398137)
      ·
        refine ⟨6505581224372248681798603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8674108299162998242398137 6505581224372248681798603)
        ·
          refine ⟨9758371836558373022697905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6505581224372248681798603 9758371836558373022697905)
          ·
            refine ⟨7318778877418779767023429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9758371836558373022697905 7318778877418779767023429)
            ·
              refine ⟨1372271039516021206316893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7318778877418779767023429 1372271039516021206316893)
              ·
                refine ⟨514601639818507952368835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1372271039516021206316893 514601639818507952368835)
                ·
                  refine ⟨771902459727761928553253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 514601639818507952368835 771902459727761928553253)
                  ·
                    refine ⟨144731711198955361603735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 771902459727761928553253 144731711198955361603735)
                    ·
                      rfl

theorem cell22_422796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 1, 4].length) (baseStart_422796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_422796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_422796 prefixEnd_422796 := by exact prefixLift 422796
  have htrace : WordTrace (prefixWord ++ tailWord_422796) baseStart_422796 baseEnd_422796 := by
    simpa [prefixWord, tailWord_422796, baseEnd_422796] using wordTrace_append hprefix tailTrace_422796
  have hstable : (prefixWord ++ tailWord_422796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422796).length < 2 ^ (prefixWord ++ tailWord_422796).sum := by decide
  have hdescent : baseEnd_422796 < baseStart_422796 := by decide
  rcases family_descends (prefixWord ++ tailWord_422796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422839 : List Nat := [1, 1, 3, 1, 3, 1, 4, 8]
def baseStart_422839 : Nat := 118140960795 + 422839 * 2 ^ 59
def prefixEnd_422839 : Nat := 4983230072969 + 3 ^ 40 * 422839 * 2
def baseEnd_422839 : Nat := 16082936775301953642067

theorem tailTrace_422839 : CollatzResearch.WordTrace tailWord_422839 prefixEnd_422839 16082936775301953642067 := by
  unfold tailWord_422839
  simp only [CollatzResearch.WordTrace]
  refine ⟨15422205315133992996967571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10281470210089328664645047 15422205315133992996967571)
  ·
    refine ⟨23133307972700989495451357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15422205315133992996967571 23133307972700989495451357)
    ·
      refine ⟨8674990489762871060794259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23133307972700989495451357 8674990489762871060794259)
      ·
        refine ⟨13012485734644306591191389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8674990489762871060794259 13012485734644306591191389)
        ·
          refine ⟨4879682150491614971696771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13012485734644306591191389 4879682150491614971696771)
          ·
            refine ⟨7319523225737422457545157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4879682150491614971696771 7319523225737422457545157)
            ·
              refine ⟨1372410604825766710789717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7319523225737422457545157 1372410604825766710789717)
              ·
                refine ⟨16082936775301953642067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1372410604825766710789717 16082936775301953642067)
                ·
                  rfl

theorem cell22_422839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 8].length) (baseStart_422839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_422839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_422839 prefixEnd_422839 := by exact prefixLift 422839
  have htrace : WordTrace (prefixWord ++ tailWord_422839) baseStart_422839 baseEnd_422839 := by
    simpa [prefixWord, tailWord_422839, baseEnd_422839] using wordTrace_append hprefix tailTrace_422839
  have hstable : (prefixWord ++ tailWord_422839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422839).length < 2 ^ (prefixWord ++ tailWord_422839).sum := by decide
  have hdescent : baseEnd_422839 < baseStart_422839 := by decide
  rcases family_descends (prefixWord ++ tailWord_422839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422841 : List Nat := [1, 2, 1, 4, 2, 2, 1, 3, 2, 4]
def baseStart_422841 : Nat := 118140960795 + 422841 * 2 ^ 59
def prefixEnd_422841 : Nat := 4983230072969 + 3 ^ 40 * 422841 * 2
def baseEnd_422841 : Nat := 144747115618590244228597

theorem tailTrace_422841 : CollatzResearch.WordTrace tailWord_422841 prefixEnd_422841 144747115618590244228597 := by
  unfold tailWord_422841
  simp only [CollatzResearch.WordTrace]
  refine ⟨15422278261126747338540377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10281518840751164892360251 15422278261126747338540377)
  ·
    refine ⟨11566708695845060503905283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15422278261126747338540377 11566708695845060503905283)
    ·
      refine ⟨17350063043767590755857925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11566708695845060503905283 17350063043767590755857925)
      ·
        refine ⟨3253136820706423266723361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17350063043767590755857925 3253136820706423266723361)
        ·
          refine ⟨2439852615529817450042521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3253136820706423266723361 2439852615529817450042521)
          ·
            refine ⟨1829889461647363087531891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2439852615529817450042521 1829889461647363087531891)
            ·
              refine ⟨2744834192471044631297837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1829889461647363087531891 2744834192471044631297837)
              ·
                refine ⟨1029312822176641736736689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2744834192471044631297837 1029312822176641736736689)
                ·
                  refine ⟨771984616632481302552517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1029312822176641736736689 771984616632481302552517)
                  ·
                    refine ⟨144747115618590244228597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 771984616632481302552517 144747115618590244228597)
                    ·
                      rfl

theorem cell22_422841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 4].length) (baseStart_422841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_422841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_422841 prefixEnd_422841 := by exact prefixLift 422841
  have htrace : WordTrace (prefixWord ++ tailWord_422841) baseStart_422841 baseEnd_422841 := by
    simpa [prefixWord, tailWord_422841, baseEnd_422841] using wordTrace_append hprefix tailTrace_422841
  have hstable : (prefixWord ++ tailWord_422841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422841).length < 2 ^ (prefixWord ++ tailWord_422841).sum := by decide
  have hdescent : baseEnd_422841 < baseStart_422841 := by decide
  rcases family_descends (prefixWord ++ tailWord_422841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422856 : List Nat := [2, 1, 3, 1, 6, 9]
def baseStart_422856 : Nat := 118140960795 + 422856 * 2 ^ 59
def prefixEnd_422856 : Nat := 4983230072969 + 3 ^ 40 * 422856 * 2
def baseEnd_422856 : Nat := 1787064820063397593871

theorem tailTrace_422856 : CollatzResearch.WordTrace tailWord_422856 prefixEnd_422856 1787064820063397593871 := by
  unfold tailWord_422856
  simp only [CollatzResearch.WordTrace]
  refine ⟨7711412678036202450168211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10281883570714936600224281 7711412678036202450168211)
  ·
    refine ⟨11567119017054303675252317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7711412678036202450168211 11567119017054303675252317)
    ·
      refine ⟨4337669631395363878219619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11567119017054303675252317 4337669631395363878219619)
      ·
        refine ⟨6506504447093045817329429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4337669631395363878219619 6506504447093045817329429)
        ·
          refine ⟨304992395957486522687317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6506504447093045817329429 304992395957486522687317)
          ·
            refine ⟨1787064820063397593871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 304992395957486522687317 1787064820063397593871)
            ·
              rfl

theorem cell22_422856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 9].length) (baseStart_422856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_422856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_422856 prefixEnd_422856 := by exact prefixLift 422856
  have htrace : WordTrace (prefixWord ++ tailWord_422856) baseStart_422856 baseEnd_422856 := by
    simpa [prefixWord, tailWord_422856, baseEnd_422856] using wordTrace_append hprefix tailTrace_422856
  have hstable : (prefixWord ++ tailWord_422856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422856).length < 2 ^ (prefixWord ++ tailWord_422856).sum := by decide
  have hdescent : baseEnd_422856 < baseStart_422856 := by decide
  rcases family_descends (prefixWord ++ tailWord_422856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422905 : List Nat := [1, 2, 1, 3, 1, 3, 4, 3, 1, 3]
def baseStart_422905 : Nat := 118140960795 + 422905 * 2 ^ 59
def prefixEnd_422905 : Nat := 4983230072969 + 3 ^ 40 * 422905 * 2
def baseEnd_422905 : Nat := 144769024126515410628401

theorem tailTrace_422905 : CollatzResearch.WordTrace tailWord_422905 prefixEnd_422905 144769024126515410628401 := by
  unfold tailWord_422905
  simp only [CollatzResearch.WordTrace]
  refine ⟨15424612532894886268870169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10283075021929924179246779 15424612532894886268870169)
  ·
    refine ⟨11568459399671164701652627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15424612532894886268870169 11568459399671164701652627)
    ·
      refine ⟨17352689099506747052478941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11568459399671164701652627 17352689099506747052478941)
      ·
        refine ⟨6507258412315030144679603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17352689099506747052478941 6507258412315030144679603)
        ·
          refine ⟨9760887618472545217019405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6507258412315030144679603 9760887618472545217019405)
          ·
            refine ⟨3660332856927204456382277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9760887618472545217019405 3660332856927204456382277)
            ·
              refine ⟨686312410673850835571677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3660332856927204456382277 686312410673850835571677)
              ·
                refine ⟨257367154002694063339379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 686312410673850835571677 257367154002694063339379)
                ·
                  refine ⟨386050731004041095009069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 257367154002694063339379 386050731004041095009069)
                  ·
                    refine ⟨144769024126515410628401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 386050731004041095009069 144769024126515410628401)
                    ·
                      rfl

theorem cell22_422905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 3, 1, 3].length) (baseStart_422905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_422905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_422905 prefixEnd_422905 := by exact prefixLift 422905
  have htrace : WordTrace (prefixWord ++ tailWord_422905) baseStart_422905 baseEnd_422905 := by
    simpa [prefixWord, tailWord_422905, baseEnd_422905] using wordTrace_append hprefix tailTrace_422905
  have hstable : (prefixWord ++ tailWord_422905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422905).length < 2 ^ (prefixWord ++ tailWord_422905).sum := by decide
  have hdescent : baseEnd_422905 < baseStart_422905 := by decide
  rcases family_descends (prefixWord ++ tailWord_422905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422935 : List Nat := [1, 1, 3, 5, 1, 2, 3, 1, 5]
def baseStart_422935 : Nat := 118140960795 + 422935 * 2 ^ 59
def prefixEnd_422935 : Nat := 4983230072969 + 3 ^ 40 * 422935 * 2
def baseEnd_422935 : Nat := 48259764579868444126103

theorem tailTrace_422935 : CollatzResearch.WordTrace tailWord_422935 prefixEnd_422935 48259764579868444126103 := by
  unfold tailWord_422935
  simp only [CollatzResearch.WordTrace]
  refine ⟨15425706722786201392462259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10283804481857467594974839 15425706722786201392462259)
  ·
    refine ⟨23138560084179302088693389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15425706722786201392462259 23138560084179302088693389)
    ·
      refine ⟨8676960031567238283260021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23138560084179302088693389 8676960031567238283260021)
      ·
        refine ⟨813465002959428589055627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8676960031567238283260021 813465002959428589055627)
        ·
          refine ⟨1220197504439142883583441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 813465002959428589055627 1220197504439142883583441)
          ·
            refine ⟨915148128329357162687581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1220197504439142883583441 915148128329357162687581)
            ·
              refine ⟨343180548123508936007843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 915148128329357162687581 343180548123508936007843)
              ·
                refine ⟨514770822185263404011765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343180548123508936007843 514770822185263404011765)
                ·
                  refine ⟨48259764579868444126103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 514770822185263404011765 48259764579868444126103)
                  ·
                    rfl

theorem cell22_422935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 5].length) (baseStart_422935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_422935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_422935 prefixEnd_422935 := by exact prefixLift 422935
  have htrace : WordTrace (prefixWord ++ tailWord_422935) baseStart_422935 baseEnd_422935 := by
    simpa [prefixWord, tailWord_422935, baseEnd_422935] using wordTrace_append hprefix tailTrace_422935
  have hstable : (prefixWord ++ tailWord_422935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422935).length < 2 ^ (prefixWord ++ tailWord_422935).sum := by decide
  have hdescent : baseEnd_422935 < baseStart_422935 := by decide
  rcases family_descends (prefixWord ++ tailWord_422935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422961 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 3, 5]
def baseStart_422961 : Nat := 118140960795 + 422961 * 2 ^ 59
def prefixEnd_422961 : Nat := 4983230072969 + 3 ^ 40 * 422961 * 2
def baseEnd_422961 : Nat := 144788194070949931228229

theorem tailTrace_422961 : CollatzResearch.WordTrace tailWord_422961 prefixEnd_422961 144788194070949931228229 := by
  unfold tailWord_422961
  simp only [CollatzResearch.WordTrace]
  refine ⟨15426655020692007832908737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10284436680461338555272491 15426655020692007832908737)
  ·
    refine ⟨11569991265519005874681553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15426655020692007832908737 11569991265519005874681553)
    ·
      refine ⟨8677493449139254406011165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11569991265519005874681553 8677493449139254406011165)
      ·
        refine ⟨3254060043427220402254187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8677493449139254406011165 3254060043427220402254187)
        ·
          refine ⟨4881090065140830603381281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3254060043427220402254187 4881090065140830603381281)
          ·
            refine ⟨3660817548855622952535961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4881090065140830603381281 3660817548855622952535961)
            ·
              refine ⟨2745613161641717214401971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3660817548855622952535961 2745613161641717214401971)
              ·
                refine ⟨4118419742462575821602957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2745613161641717214401971 4118419742462575821602957)
                ·
                  refine ⟨1544407403423465933101109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4118419742462575821602957 1544407403423465933101109)
                  ·
                    refine ⟨144788194070949931228229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1544407403423465933101109 144788194070949931228229)
                    ·
                      rfl

theorem cell22_422961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_422961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_422961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_422961 prefixEnd_422961 := by exact prefixLift 422961
  have htrace : WordTrace (prefixWord ++ tailWord_422961) baseStart_422961 baseEnd_422961 := by
    simpa [prefixWord, tailWord_422961, baseEnd_422961] using wordTrace_append hprefix tailTrace_422961
  have hstable : (prefixWord ++ tailWord_422961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422961).length < 2 ^ (prefixWord ++ tailWord_422961).sum := by decide
  have hdescent : baseEnd_422961 < baseStart_422961 := by decide
  rcases family_descends (prefixWord ++ tailWord_422961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423010 : List Nat := [3, 3, 2, 2, 1, 1, 1, 3, 2, 4]
def baseStart_423010 : Nat := 118140960795 + 423010 * 2 ^ 59
def prefixEnd_423010 : Nat := 4983230072969 + 3 ^ 40 * 423010 * 2
def baseEnd_423010 : Nat := 144804967772330136753079

theorem tailTrace_423010 : CollatzResearch.WordTrace tailWord_423010 prefixEnd_423010 144804967772330136753079 := by
  unfold tailWord_423010
  simp only [CollatzResearch.WordTrace]
  refine ⟨3857110549378622300360621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10285628131676326134294989 3857110549378622300360621)
  ·
    refine ⟨1446416456016983362635233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3857110549378622300360621 1446416456016983362635233)
    ·
      refine ⟨1084812342012737521976425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1446416456016983362635233 1084812342012737521976425)
      ·
        refine ⟨813609256509553141482319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1084812342012737521976425 813609256509553141482319)
        ·
          refine ⟨1220413884764329712223479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 813609256509553141482319 1220413884764329712223479)
          ·
            refine ⟨1830620827146494568335219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1220413884764329712223479 1830620827146494568335219)
            ·
              refine ⟨2745931240719741852502829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1830620827146494568335219 2745931240719741852502829)
              ·
                refine ⟨1029724215269903194688561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2745931240719741852502829 1029724215269903194688561)
                ·
                  refine ⟨772293161452427396016421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1029724215269903194688561 772293161452427396016421)
                  ·
                    refine ⟨144804967772330136753079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 772293161452427396016421 144804967772330136753079)
                    ·
                      rfl

theorem cell22_423010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_423010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_423010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_423010 prefixEnd_423010 := by exact prefixLift 423010
  have htrace : WordTrace (prefixWord ++ tailWord_423010) baseStart_423010 baseEnd_423010 := by
    simpa [prefixWord, tailWord_423010, baseEnd_423010] using wordTrace_append hprefix tailTrace_423010
  have hstable : (prefixWord ++ tailWord_423010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423010).length < 2 ^ (prefixWord ++ tailWord_423010).sum := by decide
  have hdescent : baseEnd_423010 < baseStart_423010 := by decide
  rcases family_descends (prefixWord ++ tailWord_423010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423029 : List Nat := [1, 3, 4, 3, 1, 1, 2, 2, 2, 3]
def baseStart_423029 : Nat := 118140960795 + 423029 * 2 ^ 59
def prefixEnd_423029 : Nat := 4983230072969 + 3 ^ 40 * 423029 * 2
def baseEnd_423029 : Nat := 144811471860620420528021

theorem tailTrace_423029 : CollatzResearch.WordTrace tailWord_423029 prefixEnd_423029 144811471860620420528021 := by
  unfold tailWord_423029
  simp only [CollatzResearch.WordTrace]
  refine ⟨15429135184445655446384141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10286090122963770297589427 15429135184445655446384141)
  ·
    refine ⟨5785925694167120792394053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15429135184445655446384141 5785925694167120792394053)
    ·
      refine ⟨1084861067656335148573885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5785925694167120792394053 1084861067656335148573885)
      ·
        refine ⟨406822900371125680715207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1084861067656335148573885 406822900371125680715207)
        ·
          refine ⟨610234350556688521072811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406822900371125680715207 610234350556688521072811)
          ·
            refine ⟨915351525835032781609217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 610234350556688521072811 915351525835032781609217)
            ·
              refine ⟨686513644376274586206913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 915351525835032781609217 686513644376274586206913)
              ·
                refine ⟨514885233282205939655185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 686513644376274586206913 514885233282205939655185)
                ·
                  refine ⟨386163924961654454741389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 514885233282205939655185 386163924961654454741389)
                  ·
                    refine ⟨144811471860620420528021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 386163924961654454741389 144811471860620420528021)
                    ·
                      rfl

theorem cell22_423029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_423029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_423029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_423029 prefixEnd_423029 := by exact prefixLift 423029
  have htrace : WordTrace (prefixWord ++ tailWord_423029) baseStart_423029 baseEnd_423029 := by
    simpa [prefixWord, tailWord_423029, baseEnd_423029] using wordTrace_append hprefix tailTrace_423029
  have hstable : (prefixWord ++ tailWord_423029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423029).length < 2 ^ (prefixWord ++ tailWord_423029).sum := by decide
  have hdescent : baseEnd_423029 < baseStart_423029 := by decide
  rcases family_descends (prefixWord ++ tailWord_423029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423149 : List Nat := [1, 5, 1, 2, 2, 2, 3, 2, 4]
def baseStart_423149 : Nat := 118140960795 + 423149 * 2 ^ 59
def prefixEnd_423149 : Nat := 4983230072969 + 3 ^ 40 * 423149 * 2
def baseEnd_423149 : Nat := 48284183437660035842551

theorem tailTrace_423149 : CollatzResearch.WordTrace tailWord_423149 prefixEnd_423149 48284183437660035842551 := by
  unfold tailWord_423149
  simp only [CollatzResearch.WordTrace]
  refine ⟨15433511944010915940752501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10289007962673943960501667 15433511944010915940752501)
  ·
    refine ⟨1446891744751023369445547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15433511944010915940752501 1446891744751023369445547)
    ·
      refine ⟨2170337617126535054168321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1446891744751023369445547 2170337617126535054168321)
      ·
        refine ⟨1627753212844901290626241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2170337617126535054168321 1627753212844901290626241)
        ·
          refine ⟨1220814909633675967969681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1627753212844901290626241 1220814909633675967969681)
          ·
            refine ⟨915611182225256975977261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1220814909633675967969681 915611182225256975977261)
            ·
              refine ⟨343354193334471365991473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 915611182225256975977261 343354193334471365991473)
              ·
                refine ⟨257515645000853524493605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 343354193334471365991473 257515645000853524493605)
                ·
                  refine ⟨48284183437660035842551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 257515645000853524493605 48284183437660035842551)
                  ·
                    rfl

theorem cell22_423149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_423149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_423149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_423149 prefixEnd_423149 := by exact prefixLift 423149
  have htrace : WordTrace (prefixWord ++ tailWord_423149) baseStart_423149 baseEnd_423149 := by
    simpa [prefixWord, tailWord_423149, baseEnd_423149] using wordTrace_append hprefix tailTrace_423149
  have hstable : (prefixWord ++ tailWord_423149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423149).length < 2 ^ (prefixWord ++ tailWord_423149).sum := by decide
  have hdescent : baseEnd_423149 < baseStart_423149 := by decide
  rcases family_descends (prefixWord ++ tailWord_423149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423205 : List Nat := [1, 3, 1, 2, 4, 1, 1, 4, 5]
def baseStart_423205 : Nat := 118140960795 + 423205 * 2 ^ 59
def prefixEnd_423205 : Nat := 4983230072969 + 3 ^ 40 * 423205 * 2
def baseEnd_423205 : Nat := 48290573419138209375827

theorem tailTrace_423205 : CollatzResearch.WordTrace tailWord_423205 prefixEnd_423205 48290573419138209375827 := by
  unfold tailWord_423205
  simp only [CollatzResearch.WordTrace]
  refine ⟨15435554431808037504791069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10290369621205358336527379 15435554431808037504791069)
  ·
    refine ⟨5788332911928014064296651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15435554431808037504791069 5788332911928014064296651)
    ·
      refine ⟨8682499367892021096444977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5788332911928014064296651 8682499367892021096444977)
      ·
        refine ⟨6511874525919015822333733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8682499367892021096444977 6511874525919015822333733)
        ·
          refine ⟨1220976473609815466687575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6511874525919015822333733 1220976473609815466687575)
          ·
            refine ⟨1831464710414723200031363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1220976473609815466687575 1831464710414723200031363)
            ·
              refine ⟨2747197065622084800047045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1831464710414723200031363 2747197065622084800047045)
              ·
                refine ⟨515099449804140900008821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2747197065622084800047045 515099449804140900008821)
                ·
                  refine ⟨48290573419138209375827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 515099449804140900008821 48290573419138209375827)
                  ·
                    rfl

theorem cell22_423205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 5].length) (baseStart_423205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_423205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_423205 prefixEnd_423205 := by exact prefixLift 423205
  have htrace : WordTrace (prefixWord ++ tailWord_423205) baseStart_423205 baseEnd_423205 := by
    simpa [prefixWord, tailWord_423205, baseEnd_423205] using wordTrace_append hprefix tailTrace_423205
  have hstable : (prefixWord ++ tailWord_423205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423205).length < 2 ^ (prefixWord ++ tailWord_423205).sum := by decide
  have hdescent : baseEnd_423205 < baseStart_423205 := by decide
  rcases family_descends (prefixWord ++ tailWord_423205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423235 : List Nat := [1, 1, 1, 3, 1, 3, 1, 6, 1, 4]
def baseStart_423235 : Nat := 118140960795 + 423235 * 2 ^ 59
def prefixEnd_423235 : Nat := 4983230072969 + 3 ^ 40 * 423235 * 2
def baseEnd_423235 : Nat := 144881989870504549877389

theorem tailTrace_423235 : CollatzResearch.WordTrace tailWord_423235 prefixEnd_423235 144881989870504549877389 := by
  unfold tailWord_423235
  simp only [CollatzResearch.WordTrace]
  refine ⟨15436648621699352628383159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10291099081132901752255439 15436648621699352628383159)
  ·
    refine ⟨23154972932549028942574739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15436648621699352628383159 23154972932549028942574739)
    ·
      refine ⟨34732459398823543413862109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23154972932549028942574739 34732459398823543413862109)
      ·
        refine ⟨13024672274558828780198291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34732459398823543413862109 13024672274558828780198291)
        ·
          refine ⟨19537008411838243170297437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13024672274558828780198291 19537008411838243170297437)
          ·
            refine ⟨7326378154439341188861539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19537008411838243170297437 7326378154439341188861539)
            ·
              refine ⟨10989567231659011783292309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7326378154439341188861539 10989567231659011783292309)
              ·
                refine ⟨515135963984016177341827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10989567231659011783292309 515135963984016177341827)
                ·
                  refine ⟨772703945976024266012741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 515135963984016177341827 772703945976024266012741)
                  ·
                    refine ⟨144881989870504549877389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 772703945976024266012741 144881989870504549877389)
                    ·
                      rfl

theorem cell22_423235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 4].length) (baseStart_423235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_423235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_423235 prefixEnd_423235 := by exact prefixLift 423235
  have htrace : WordTrace (prefixWord ++ tailWord_423235) baseStart_423235 baseEnd_423235 := by
    simpa [prefixWord, tailWord_423235, baseEnd_423235] using wordTrace_append hprefix tailTrace_423235
  have hstable : (prefixWord ++ tailWord_423235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423235).length < 2 ^ (prefixWord ++ tailWord_423235).sum := by decide
  have hdescent : baseEnd_423235 < baseStart_423235 := by decide
  rcases family_descends (prefixWord ++ tailWord_423235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423252 : List Nat := [2, 4, 1, 1, 2, 1, 3, 3, 1, 4]
def baseStart_423252 : Nat := 118140960795 + 423252 * 2 ^ 59
def prefixEnd_423252 : Nat := 4983230072969 + 3 ^ 40 * 423252 * 2
def baseEnd_423252 : Nat := 144887809317922172202337

theorem tailTrace_423252 : CollatzResearch.WordTrace tailWord_423252 prefixEnd_423252 144887809317922172202337 := by
  unfold tailWord_423252
  simp only [CollatzResearch.WordTrace]
  refine ⟨7718634331318882265876005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10291512441758509687834673 7718634331318882265876005)
  ·
    refine ⟨1447243937122290424851751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7718634331318882265876005 1447243937122290424851751)
    ·
      refine ⟨2170865905683435637277627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1447243937122290424851751 2170865905683435637277627)
      ·
        refine ⟨3256298858525153455916441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2170865905683435637277627 3256298858525153455916441)
        ·
          refine ⟨2442224143893865091937331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3256298858525153455916441 2442224143893865091937331)
          ·
            refine ⟨3663336215840797637905997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2442224143893865091937331 3663336215840797637905997)
            ·
              refine ⟨1373751080940299114214749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3663336215840797637905997 1373751080940299114214749)
              ·
                refine ⟨515156655352612167830531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1373751080940299114214749 515156655352612167830531)
                ·
                  refine ⟨772734983028918251745797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 515156655352612167830531 772734983028918251745797)
                  ·
                    refine ⟨144887809317922172202337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 772734983028918251745797 144887809317922172202337)
                    ·
                      rfl

theorem cell22_423252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_423252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_423252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_423252 prefixEnd_423252 := by exact prefixLift 423252
  have htrace : WordTrace (prefixWord ++ tailWord_423252) baseStart_423252 baseEnd_423252 := by
    simpa [prefixWord, tailWord_423252, baseEnd_423252] using wordTrace_append hprefix tailTrace_423252
  have hstable : (prefixWord ++ tailWord_423252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423252).length < 2 ^ (prefixWord ++ tailWord_423252).sum := by decide
  have hdescent : baseEnd_423252 < baseStart_423252 := by decide
  rcases family_descends (prefixWord ++ tailWord_423252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423267 : List Nat := [1, 1, 1, 5, 2, 2, 2, 4, 4]
def baseStart_423267 : Nat := 118140960795 + 423267 * 2 ^ 59
def prefixEnd_423267 : Nat := 4983230072969 + 3 ^ 40 * 423267 * 2
def baseEnd_423267 : Nat := 48297648041489044359097

theorem tailTrace_423267 : CollatzResearch.WordTrace tailWord_423267 prefixEnd_423267 48297648041489044359097 := by
  unfold tailWord_423267
  simp only [CollatzResearch.WordTrace]
  refine ⟨15437815757583422093548055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10291877171722281395698703 15437815757583422093548055)
  ·
    refine ⟨23156723636375133140322083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15437815757583422093548055 23156723636375133140322083)
    ·
      refine ⟨34735085454562699710483125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23156723636375133140322083 34735085454562699710483125)
      ·
        refine ⟨3256414261365253097857793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34735085454562699710483125 3256414261365253097857793)
        ·
          refine ⟨2442310696023939823393345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3256414261365253097857793 2442310696023939823393345)
          ·
            refine ⟨1831733022017954867545009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2442310696023939823393345 1831733022017954867545009)
            ·
              refine ⟨1373799766513466150658757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1831733022017954867545009 1373799766513466150658757)
              ·
                refine ⟨257587456221274903248517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1373799766513466150658757 257587456221274903248517)
                ·
                  refine ⟨48297648041489044359097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 257587456221274903248517 48297648041489044359097)
                  ·
                    rfl

theorem cell22_423267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 4, 4].length) (baseStart_423267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_423267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_423267 prefixEnd_423267 := by exact prefixLift 423267
  have htrace : WordTrace (prefixWord ++ tailWord_423267) baseStart_423267 baseEnd_423267 := by
    simpa [prefixWord, tailWord_423267, baseEnd_423267] using wordTrace_append hprefix tailTrace_423267
  have hstable : (prefixWord ++ tailWord_423267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423267).length < 2 ^ (prefixWord ++ tailWord_423267).sum := by decide
  have hdescent : baseEnd_423267 < baseStart_423267 := by decide
  rcases family_descends (prefixWord ++ tailWord_423267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423417 : List Nat := [1, 2, 1, 3, 1, 2, 1, 4, 4, 3]
def baseStart_423417 : Nat := 118140960795 + 423417 * 2 ^ 59
def prefixEnd_423417 : Nat := 4983230072969 + 3 ^ 40 * 423417 * 2
def baseEnd_423417 : Nat := 144944292189916741826831

theorem tailTrace_423417 : CollatzResearch.WordTrace tailWord_423417 prefixEnd_423417 144944292189916741826831 := by
  unfold tailWord_423417
  simp only [CollatzResearch.WordTrace]
  refine ⟨15443286707039997711508505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10295524471359998474339003 15443286707039997711508505)
  ·
    refine ⟨11582465030279998283631379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15443286707039997711508505 11582465030279998283631379)
    ·
      refine ⟨17373697545419997425447069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11582465030279998283631379 17373697545419997425447069)
      ·
        refine ⟨6515136579532499034542651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17373697545419997425447069 6515136579532499034542651)
        ·
          refine ⟨9772704869298748551813977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6515136579532499034542651 9772704869298748551813977)
          ·
            refine ⟨7329528651974061413860483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9772704869298748551813977 7329528651974061413860483)
            ·
              refine ⟨10994292977961092120790725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7329528651974061413860483 10994292977961092120790725)
              ·
                refine ⟨2061429933367704772648261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10994292977961092120790725 2061429933367704772648261)
                ·
                  refine ⟨386518112506444644871549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2061429933367704772648261 386518112506444644871549)
                  ·
                    refine ⟨144944292189916741826831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 386518112506444644871549 144944292189916741826831)
                    ·
                      rfl

theorem cell22_423417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 4, 3].length) (baseStart_423417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_423417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_423417 prefixEnd_423417 := by exact prefixLift 423417
  have htrace : WordTrace (prefixWord ++ tailWord_423417) baseStart_423417 baseEnd_423417 := by
    simpa [prefixWord, tailWord_423417, baseEnd_423417] using wordTrace_append hprefix tailTrace_423417
  have hstable : (prefixWord ++ tailWord_423417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423417).length < 2 ^ (prefixWord ++ tailWord_423417).sum := by decide
  have hdescent : baseEnd_423417 < baseStart_423417 := by decide
  rcases family_descends (prefixWord ++ tailWord_423417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423421 : List Nat := [1, 4, 1, 1, 1, 6, 2, 1, 1, 4]
def baseStart_423421 : Nat := 118140960795 + 423421 * 2 ^ 59
def prefixEnd_423421 : Nat := 4983230072969 + 3 ^ 40 * 423421 * 2
def baseEnd_423421 : Nat := 144945661471662064726819

theorem tailTrace_423421 : CollatzResearch.WordTrace tailWord_423421 prefixEnd_423421 144945661471662064726819 := by
  unfold tailWord_423421
  simp only [CollatzResearch.WordTrace]
  refine ⟨15443432599025506394654117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10295621732683670929769411 15443432599025506394654117)
  ·
    refine ⟨2895643612317282448997647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15443432599025506394654117 2895643612317282448997647)
    ·
      refine ⟨4343465418475923673496471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2895643612317282448997647 4343465418475923673496471)
      ·
        refine ⟨6515198127713885510244707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4343465418475923673496471 6515198127713885510244707)
        ·
          refine ⟨9772797191570828265367061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6515198127713885510244707 9772797191570828265367061)
          ·
            refine ⟨458099868354882574939081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9772797191570828265367061 458099868354882574939081)
            ·
              refine ⟨343574901266161931204311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 458099868354882574939081 343574901266161931204311)
              ·
                refine ⟨515362351899242896806467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343574901266161931204311 515362351899242896806467)
                ·
                  refine ⟨773043527848864345209701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 515362351899242896806467 773043527848864345209701)
                  ·
                    refine ⟨144945661471662064726819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 773043527848864345209701 144945661471662064726819)
                    ·
                      rfl

theorem cell22_423421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_423421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_423421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_423421 prefixEnd_423421 := by exact prefixLift 423421
  have htrace : WordTrace (prefixWord ++ tailWord_423421) baseStart_423421 baseEnd_423421 := by
    simpa [prefixWord, tailWord_423421, baseEnd_423421] using wordTrace_append hprefix tailTrace_423421
  have hstable : (prefixWord ++ tailWord_423421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423421).length < 2 ^ (prefixWord ++ tailWord_423421).sum := by decide
  have hdescent : baseEnd_423421 < baseStart_423421 := by decide
  rcases family_descends (prefixWord ++ tailWord_423421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423432 : List Nat := [2, 1, 3, 2, 1, 1, 2, 4, 2, 4]
def baseStart_423432 : Nat := 118140960795 + 423432 * 2 ^ 59
def prefixEnd_423432 : Nat := 4983230072969 + 3 ^ 40 * 423432 * 2
def baseEnd_423432 : Nat := 144949426996461702701785

theorem tailTrace_423432 : CollatzResearch.WordTrace tailWord_423432 prefixEnd_423432 144949426996461702701785 := by
  unfold tailWord_423432
  simp only [CollatzResearch.WordTrace]
  refine ⟨7721916900992827636652275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10295889201323770182203033 7721916900992827636652275)
  ·
    refine ⟨11582875351489241454978413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7721916900992827636652275 11582875351489241454978413)
    ·
      refine ⟨4343578256808465545616905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11582875351489241454978413 4343578256808465545616905)
      ·
        refine ⟨3257683692606349159212679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4343578256808465545616905 3257683692606349159212679)
        ·
          refine ⟨4886525538909523738819019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3257683692606349159212679 4886525538909523738819019)
          ·
            refine ⟨7329788308364285608228529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4886525538909523738819019 7329788308364285608228529)
            ·
              refine ⟨5497341231273214206171397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7329788308364285608228529 5497341231273214206171397)
              ·
                refine ⟨1030751480863727663657137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5497341231273214206171397 1030751480863727663657137)
                ·
                  refine ⟨773063610647795747742853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1030751480863727663657137 773063610647795747742853)
                  ·
                    refine ⟨144949426996461702701785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 773063610647795747742853 144949426996461702701785)
                    ·
                      rfl

theorem cell22_423432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_423432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_423432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_423432 prefixEnd_423432 := by exact prefixLift 423432
  have htrace : WordTrace (prefixWord ++ tailWord_423432) baseStart_423432 baseEnd_423432 := by
    simpa [prefixWord, tailWord_423432, baseEnd_423432] using wordTrace_append hprefix tailTrace_423432
  have hstable : (prefixWord ++ tailWord_423432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423432).length < 2 ^ (prefixWord ++ tailWord_423432).sum := by decide
  have hdescent : baseEnd_423432 < baseStart_423432 := by decide
  rcases family_descends (prefixWord ++ tailWord_423432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423434 : List Nat := [3, 1, 2, 2, 2, 3, 1, 1, 4, 3]
def baseStart_423434 : Nat := 118140960795 + 423434 * 2 ^ 59
def prefixEnd_423434 : Nat := 4983230072969 + 3 ^ 40 * 423434 * 2
def baseEnd_423434 : Nat := 144950111637334364151779

theorem tailTrace_423434 : CollatzResearch.WordTrace tailWord_423434 prefixEnd_423434 144950111637334364151779 := by
  unfold tailWord_423434
  simp only [CollatzResearch.WordTrace]
  refine ⟨3860976686994602403719339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10295937831985606409918237 3860976686994602403719339)
  ·
    refine ⟨5791465030491903605579009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3860976686994602403719339 5791465030491903605579009)
    ·
      refine ⟨4343598772868927704184257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5791465030491903605579009 4343598772868927704184257)
      ·
        refine ⟨3257699079651695778138193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4343598772868927704184257 3257699079651695778138193)
        ·
          refine ⟨2443274309738771833603645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3257699079651695778138193 2443274309738771833603645)
          ·
            refine ⟨916227866152039437601367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2443274309738771833603645 916227866152039437601367)
            ·
              refine ⟨1374341799228059156402051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 916227866152039437601367 1374341799228059156402051)
              ·
                refine ⟨2061512698842088734603077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1374341799228059156402051 2061512698842088734603077)
                ·
                  refine ⟨386533631032891637738077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2061512698842088734603077 386533631032891637738077)
                  ·
                    refine ⟨144950111637334364151779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 386533631032891637738077 144950111637334364151779)
                    ·
                      rfl

theorem cell22_423434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_423434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_423434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_423434 prefixEnd_423434 := by exact prefixLift 423434
  have htrace : WordTrace (prefixWord ++ tailWord_423434) baseStart_423434 baseEnd_423434 := by
    simpa [prefixWord, tailWord_423434, baseEnd_423434] using wordTrace_append hprefix tailTrace_423434
  have hstable : (prefixWord ++ tailWord_423434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423434).length < 2 ^ (prefixWord ++ tailWord_423434).sum := by decide
  have hdescent : baseEnd_423434 < baseStart_423434 := by decide
  rcases family_descends (prefixWord ++ tailWord_423434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423464 : List Nat := [2, 1, 5, 2, 2, 1, 1, 8]
def baseStart_423464 : Nat := 118140960795 + 423464 * 2 ^ 59
def prefixEnd_423464 : Nat := 4983230072969 + 3 ^ 40 * 423464 * 2
def baseEnd_423464 : Nat := 16106709027824920655743

theorem tailTrace_423464 : CollatzResearch.WordTrace tailWord_423464 prefixEnd_423464 16106709027824920655743 := by
  unfold tailWord_423464
  simp only [CollatzResearch.WordTrace]
  refine ⟨7722500468934862369234723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10296667291913149825646297 7722500468934862369234723)
  ·
    refine ⟨11583750703402293553852085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7722500468934862369234723 11583750703402293553852085)
    ·
      refine ⟨1085976628443965020673633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11583750703402293553852085 1085976628443965020673633)
      ·
        refine ⟨814482471332973765505225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1085976628443965020673633 814482471332973765505225)
        ·
          refine ⟨610861853499730324128919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 814482471332973765505225 610861853499730324128919)
          ·
            refine ⟨916292780249595486193379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 610861853499730324128919 916292780249595486193379)
            ·
              refine ⟨1374439170374393229290069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 916292780249595486193379 1374439170374393229290069)
              ·
                refine ⟨16106709027824920655743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1374439170374393229290069 16106709027824920655743)
                ·
                  rfl

theorem cell22_423464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 8].length) (baseStart_423464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_423464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_423464 prefixEnd_423464 := by exact prefixLift 423464
  have htrace : WordTrace (prefixWord ++ tailWord_423464) baseStart_423464 baseEnd_423464 := by
    simpa [prefixWord, tailWord_423464, baseEnd_423464] using wordTrace_append hprefix tailTrace_423464
  have hstable : (prefixWord ++ tailWord_423464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423464).length < 2 ^ (prefixWord ++ tailWord_423464).sum := by decide
  have hdescent : baseEnd_423464 < baseStart_423464 := by decide
  rcases family_descends (prefixWord ++ tailWord_423464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423552 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 3, 5]
def baseStart_423552 : Nat := 118140960795 + 423552 * 2 ^ 59
def prefixEnd_423552 : Nat := 4983230072969 + 3 ^ 40 * 423552 * 2
def baseEnd_423552 : Nat := 144990505448821389701417

theorem tailTrace_423552 : CollatzResearch.WordTrace tailWord_423552 prefixEnd_423552 144990505448821389701417 := by
  unfold tailWord_423552
  simp only [CollatzResearch.WordTrace]
  refine ⟨7724105280775457883836455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10298807041033943845115273 7724105280775457883836455)
  ·
    refine ⟨11586157921163186825754683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7724105280775457883836455 11586157921163186825754683)
    ·
      refine ⟨17379236881744780238632025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11586157921163186825754683 17379236881744780238632025)
      ·
        refine ⟨13034427661308585178974019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17379236881744780238632025 13034427661308585178974019)
        ·
          refine ⟨19551641491962877768461029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13034427661308585178974019 19551641491962877768461029)
          ·
            refine ⟨3665932779743039581586443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19551641491962877768461029 3665932779743039581586443)
            ·
              refine ⟨5498899169614559372379665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3665932779743039581586443 5498899169614559372379665)
              ·
                refine ⟨4124174377210919529284749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5498899169614559372379665 4124174377210919529284749)
                ·
                  refine ⟨1546565391454094823481781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4124174377210919529284749 1546565391454094823481781)
                  ·
                    refine ⟨144990505448821389701417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1546565391454094823481781 144990505448821389701417)
                    ·
                      rfl

theorem cell22_423552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 3, 5].length) (baseStart_423552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_423552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_423552 prefixEnd_423552 := by exact prefixLift 423552
  have htrace : WordTrace (prefixWord ++ tailWord_423552) baseStart_423552 baseEnd_423552 := by
    simpa [prefixWord, tailWord_423552, baseEnd_423552] using wordTrace_append hprefix tailTrace_423552
  have hstable : (prefixWord ++ tailWord_423552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423552).length < 2 ^ (prefixWord ++ tailWord_423552).sum := by decide
  have hdescent : baseEnd_423552 < baseStart_423552 := by decide
  rcases family_descends (prefixWord ++ tailWord_423552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423584 : List Nat := [2, 1, 1, 4, 3, 2, 1, 1, 1, 6]
def baseStart_423584 : Nat := 118140960795 + 423584 * 2 ^ 59
def prefixEnd_423584 : Nat := 4983230072969 + 3 ^ 40 * 423584 * 2
def baseEnd_423584 : Nat := 145001459702783972901319

theorem tailTrace_423584 : CollatzResearch.WordTrace tailWord_423584 prefixEnd_423584 145001459702783972901319 := by
  unfold tailWord_423584
  simp only [CollatzResearch.WordTrace]
  refine ⟨7724688848717492616418903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10299585131623323488558537 7724688848717492616418903)
  ·
    refine ⟨11587033273076238924628355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7724688848717492616418903 11587033273076238924628355)
    ·
      refine ⟨17380549909614358386942533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11587033273076238924628355 17380549909614358386942533)
      ·
        refine ⟨3258853108052692197551725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17380549909614358386942533 3258853108052692197551725)
        ·
          refine ⟨1222069915519759574081897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3258853108052692197551725 1222069915519759574081897)
          ·
            refine ⟨916552436639819680561423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1222069915519759574081897 916552436639819680561423)
            ·
              refine ⟨1374828654959729520842135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 916552436639819680561423 1374828654959729520842135)
              ·
                refine ⟨2062242982439594281263203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1374828654959729520842135 2062242982439594281263203)
                ·
                  refine ⟨3093364473659391421894805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2062242982439594281263203 3093364473659391421894805)
                  ·
                    refine ⟨145001459702783972901319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3093364473659391421894805 145001459702783972901319)
                    ·
                      rfl

theorem cell22_423584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 1, 6].length) (baseStart_423584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_423584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_423584 prefixEnd_423584 := by exact prefixLift 423584
  have htrace : WordTrace (prefixWord ++ tailWord_423584) baseStart_423584 baseEnd_423584 := by
    simpa [prefixWord, tailWord_423584, baseEnd_423584] using wordTrace_append hprefix tailTrace_423584
  have hstable : (prefixWord ++ tailWord_423584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423584).length < 2 ^ (prefixWord ++ tailWord_423584).sum := by decide
  have hdescent : baseEnd_423584 < baseStart_423584 := by decide
  rcases family_descends (prefixWord ++ tailWord_423584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423648 : List Nat := [2, 1, 1, 3, 1, 2, 5, 3, 1, 3]
def baseStart_423648 : Nat := 118140960795 + 423648 * 2 ^ 59
def prefixEnd_423648 : Nat := 4983230072969 + 3 ^ 40 * 423648 * 2
def baseEnd_423648 : Nat := 145023368210709139301123

theorem tailTrace_423648 : CollatzResearch.WordTrace tailWord_423648 prefixEnd_423648 145023368210709139301123 := by
  unfold tailWord_423648
  simp only [CollatzResearch.WordTrace]
  refine ⟨7725855984601562081583799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10301141312802082775445065 7725855984601562081583799)
  ·
    refine ⟨11588783976902343122375699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7725855984601562081583799 11588783976902343122375699)
    ·
      refine ⟨17383175965353514683563549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11588783976902343122375699 17383175965353514683563549)
      ·
        refine ⟨6518690987007568006336331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17383175965353514683563549 6518690987007568006336331)
        ·
          refine ⟨9778036480511352009504497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6518690987007568006336331 9778036480511352009504497)
          ·
            refine ⟨7333527360383514007128373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9778036480511352009504497 7333527360383514007128373)
            ·
              refine ⟨687518190035954438168285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7333527360383514007128373 687518190035954438168285)
              ·
                refine ⟨257819321263482914313107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 687518190035954438168285 257819321263482914313107)
                ·
                  refine ⟨386728981895224371469661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 257819321263482914313107 386728981895224371469661)
                  ·
                    refine ⟨145023368210709139301123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 386728981895224371469661 145023368210709139301123)
                    ·
                      rfl

theorem cell22_423648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 3, 1, 3].length) (baseStart_423648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_423648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_423648 prefixEnd_423648 := by exact prefixLift 423648
  have htrace : WordTrace (prefixWord ++ tailWord_423648) baseStart_423648 baseEnd_423648 := by
    simpa [prefixWord, tailWord_423648, baseEnd_423648] using wordTrace_append hprefix tailTrace_423648
  have hstable : (prefixWord ++ tailWord_423648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423648).length < 2 ^ (prefixWord ++ tailWord_423648).sum := by decide
  have hdescent : baseEnd_423648 < baseStart_423648 := by decide
  rcases family_descends (prefixWord ++ tailWord_423648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423665 : List Nat := [1, 2, 2, 2, 2, 4, 3, 2, 1, 3]
def baseStart_423665 : Nat := 118140960795 + 423665 * 2 ^ 59
def prefixEnd_423665 : Nat := 4983230072969 + 3 ^ 40 * 423665 * 2
def baseEnd_423665 : Nat := 145029187658126761626071

theorem tailTrace_423665 : CollatzResearch.WordTrace tailWord_423665 prefixEnd_423665 145029187658126761626071 := by
  unfold tailWord_423665
  simp only [CollatzResearch.WordTrace]
  refine ⟨15452332010141536066536449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10301554673427690711024299 15452332010141536066536449)
  ·
    refine ⟨11589249007606152049902337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15452332010141536066536449 11589249007606152049902337)
    ·
      refine ⟨8691936755704614037426753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11589249007606152049902337 8691936755704614037426753)
      ·
        refine ⟨6518952566778460528070065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8691936755704614037426753 6518952566778460528070065)
        ·
          refine ⟨4889214425083845396052549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6518952566778460528070065 4889214425083845396052549)
          ·
            refine ⟨916727704703221011759853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4889214425083845396052549 916727704703221011759853)
            ·
              refine ⟨343772889263707879409945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 916727704703221011759853 343772889263707879409945)
              ·
                refine ⟨257829666947780909557459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 343772889263707879409945 257829666947780909557459)
                ·
                  refine ⟨386744500421671364336189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 257829666947780909557459 386744500421671364336189)
                  ·
                    refine ⟨145029187658126761626071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 386744500421671364336189 145029187658126761626071)
                    ·
                      rfl

theorem cell22_423665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 2, 1, 3].length) (baseStart_423665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_423665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_423665 prefixEnd_423665 := by exact prefixLift 423665
  have htrace : WordTrace (prefixWord ++ tailWord_423665) baseStart_423665 baseEnd_423665 := by
    simpa [prefixWord, tailWord_423665, baseEnd_423665] using wordTrace_append hprefix tailTrace_423665
  have hstable : (prefixWord ++ tailWord_423665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423665).length < 2 ^ (prefixWord ++ tailWord_423665).sum := by decide
  have hdescent : baseEnd_423665 < baseStart_423665 := by decide
  rcases family_descends (prefixWord ++ tailWord_423665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423674 : List Nat := [3, 1, 1, 1, 1, 3, 1, 4, 3, 4]
def baseStart_423674 : Nat := 118140960795 + 423674 * 2 ^ 59
def prefixEnd_423674 : Nat := 4983230072969 + 3 ^ 40 * 423674 * 2
def baseEnd_423674 : Nat := 145032268542053738151043

theorem tailTrace_423674 : CollatzResearch.WordTrace tailWord_423674 prefixEnd_423674 145032268542053738151043 := by
  unfold tailWord_423674
  simp only [CollatzResearch.WordTrace]
  refine ⟨3863165066777232650903519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10301773511405953735742717 3863165066777232650903519)
  ·
    refine ⟨5794747600165848976355279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3863165066777232650903519 5794747600165848976355279)
    ·
      refine ⟨8692121400248773464532919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5794747600165848976355279 8692121400248773464532919)
      ·
        refine ⟨13038182100373160196799379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8692121400248773464532919 13038182100373160196799379)
        ·
          refine ⟨19557273150559740295199069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13038182100373160196799379 19557273150559740295199069)
          ·
            refine ⟨7333977431459902610699651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19557273150559740295199069 7333977431459902610699651)
            ·
              refine ⟨11000966147189853916049477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7333977431459902610699651 11000966147189853916049477)
              ·
                refine ⟨2062681152598097609259277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11000966147189853916049477 2062681152598097609259277)
                ·
                  refine ⟨773505432224286603472229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2062681152598097609259277 773505432224286603472229)
                  ·
                    refine ⟨145032268542053738151043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 773505432224286603472229 145032268542053738151043)
                    ·
                      rfl

theorem cell22_423674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_423674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_423674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_423674 prefixEnd_423674 := by exact prefixLift 423674
  have htrace : WordTrace (prefixWord ++ tailWord_423674) baseStart_423674 baseEnd_423674 := by
    simpa [prefixWord, tailWord_423674, baseEnd_423674] using wordTrace_append hprefix tailTrace_423674
  have hstable : (prefixWord ++ tailWord_423674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423674).length < 2 ^ (prefixWord ++ tailWord_423674).sum := by decide
  have hdescent : baseEnd_423674 < baseStart_423674 := by decide
  rcases family_descends (prefixWord ++ tailWord_423674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423678 : List Nat := [4, 2, 2, 1, 3, 1, 1, 3, 5]
def baseStart_423678 : Nat := 118140960795 + 423678 * 2 ^ 59
def prefixEnd_423678 : Nat := 4983230072969 + 3 ^ 40 * 423678 * 2
def baseEnd_423678 : Nat := 48344545941266353683677

theorem tailTrace_423678 : CollatzResearch.WordTrace tailWord_423678 prefixEnd_423678 48344545941266353683677 := by
  unfold tailWord_423678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1931600769886804910844961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10301870772729626191173125 1931600769886804910844961)
  ·
    refine ⟨1448700577415103683133721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1931600769886804910844961 1448700577415103683133721)
    ·
      refine ⟨1086525433061327762350291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1448700577415103683133721 1086525433061327762350291)
      ·
        refine ⟨1629788149591991643525437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1086525433061327762350291 1629788149591991643525437)
        ·
          refine ⟨611170556096996866322039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1629788149591991643525437 611170556096996866322039)
          ·
            refine ⟨916755834145495299483059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611170556096996866322039 916755834145495299483059)
            ·
              refine ⟨1375133751218242949224589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 916755834145495299483059 1375133751218242949224589)
              ·
                refine ⟨515675156706841105959221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1375133751218242949224589 515675156706841105959221)
                ·
                  refine ⟨48344545941266353683677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 515675156706841105959221 48344545941266353683677)
                  ·
                    rfl

theorem cell22_423678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_423678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_423678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_423678 prefixEnd_423678 := by exact prefixLift 423678
  have htrace : WordTrace (prefixWord ++ tailWord_423678) baseStart_423678 baseEnd_423678 := by
    simpa [prefixWord, tailWord_423678, baseEnd_423678] using wordTrace_append hprefix tailTrace_423678
  have hstable : (prefixWord ++ tailWord_423678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423678).length < 2 ^ (prefixWord ++ tailWord_423678).sum := by decide
  have hdescent : baseEnd_423678 < baseStart_423678 := by decide
  rcases family_descends (prefixWord ++ tailWord_423678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423691 : List Nat := [1, 1, 1, 1, 5, 1, 5, 2, 1, 4]
def baseStart_423691 : Nat := 118140960795 + 423691 * 2 ^ 59
def prefixEnd_423691 : Nat := 4983230072969 + 3 ^ 40 * 423691 * 2
def baseEnd_423691 : Nat := 145038087989471360475991

theorem tailTrace_423691 : CollatzResearch.WordTrace tailWord_423691 prefixEnd_423691 145038087989471360475991 := by
  unfold tailWord_423691
  simp only [CollatzResearch.WordTrace]
  refine ⟨15453280308047342506982927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10302186872031561671321951 15453280308047342506982927)
  ·
    refine ⟨23179920462071013760474391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15453280308047342506982927 23179920462071013760474391)
    ·
      refine ⟨34769880693106520640711587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23179920462071013760474391 34769880693106520640711587)
      ·
        refine ⟨52154821039659780961067381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34769880693106520640711587 52154821039659780961067381)
        ·
          refine ⟨4889514472468104465100067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52154821039659780961067381 4889514472468104465100067)
          ·
            refine ⟨7334271708702156697650101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4889514472468104465100067 7334271708702156697650101)
            ·
              refine ⟨687587972690827190404697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7334271708702156697650101 687587972690827190404697)
              ·
                refine ⟨515690979518120392803523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 687587972690827190404697 515690979518120392803523)
                ·
                  refine ⟨773536469277180589205285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 515690979518120392803523 773536469277180589205285)
                  ·
                    refine ⟨145038087989471360475991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 773536469277180589205285 145038087989471360475991)
                    ·
                      rfl

theorem cell22_423691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 4].length) (baseStart_423691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_423691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_423691 prefixEnd_423691 := by exact prefixLift 423691
  have htrace : WordTrace (prefixWord ++ tailWord_423691) baseStart_423691 baseEnd_423691 := by
    simpa [prefixWord, tailWord_423691, baseEnd_423691] using wordTrace_append hprefix tailTrace_423691
  have hstable : (prefixWord ++ tailWord_423691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423691).length < 2 ^ (prefixWord ++ tailWord_423691).sum := by decide
  have hdescent : baseEnd_423691 < baseStart_423691 := by decide
  rcases family_descends (prefixWord ++ tailWord_423691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423704 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 3, 5]
def baseStart_423704 : Nat := 118140960795 + 423704 * 2 ^ 59
def prefixEnd_423704 : Nat := 4983230072969 + 3 ^ 40 * 423704 * 2
def baseEnd_423704 : Nat := 145042538155143659900951

theorem tailTrace_423704 : CollatzResearch.WordTrace tailWord_423704 prefixEnd_423704 145042538155143659900951 := by
  unfold tailWord_423704
  simp only [CollatzResearch.WordTrace]
  refine ⟨7726877228500122863603083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10302502971333497151470777 7726877228500122863603083)
  ·
    refine ⟨11590315842750184295404625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7726877228500122863603083 11590315842750184295404625)
    ·
      refine ⟨8692736882062638221553469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11590315842750184295404625 8692736882062638221553469)
      ·
        refine ⟨3259776330773489333082551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8692736882062638221553469 3259776330773489333082551)
        ·
          refine ⟨4889664496160233999623827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3259776330773489333082551 4889664496160233999623827)
          ·
            refine ⟨7334496744240350999435741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4889664496160233999623827 7334496744240350999435741)
            ·
              refine ⟨2750436279090131624788403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7334496744240350999435741 2750436279090131624788403)
              ·
                refine ⟨4125654418635197437182605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2750436279090131624788403 4125654418635197437182605)
                ·
                  refine ⟨1547120406988199038943477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4125654418635197437182605 1547120406988199038943477)
                  ·
                    refine ⟨145042538155143659900951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1547120406988199038943477 145042538155143659900951)
                    ·
                      rfl

theorem cell22_423704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_423704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_423704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_423704 prefixEnd_423704 := by exact prefixLift 423704
  have htrace : WordTrace (prefixWord ++ tailWord_423704) baseStart_423704 baseEnd_423704 := by
    simpa [prefixWord, tailWord_423704, baseEnd_423704] using wordTrace_append hprefix tailTrace_423704
  have hstable : (prefixWord ++ tailWord_423704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423704).length < 2 ^ (prefixWord ++ tailWord_423704).sum := by decide
  have hdescent : baseEnd_423704 < baseStart_423704 := by decide
  rcases family_descends (prefixWord ++ tailWord_423704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423708 : List Nat := [2, 2, 3, 1, 1, 2, 5, 1, 1, 4]
def baseStart_423708 : Nat := 118140960795 + 423708 * 2 ^ 59
def prefixEnd_423708 : Nat := 4983230072969 + 3 ^ 40 * 423708 * 2
def baseEnd_423708 : Nat := 145043907436888982800939

theorem tailTrace_423708 : CollatzResearch.WordTrace tailWord_423708 prefixEnd_423708 145043907436888982800939 := by
  unfold tailWord_423708
  simp only [CollatzResearch.WordTrace]
  refine ⟨7726950174492877205175889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10302600232657169606901185 7726950174492877205175889)
  ·
    refine ⟨5795212630869657903881917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7726950174492877205175889 5795212630869657903881917)
    ·
      refine ⟨2173204736576121713955719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5795212630869657903881917 2173204736576121713955719)
      ·
        refine ⟨3259807104864182570933579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2173204736576121713955719 3259807104864182570933579)
        ·
          refine ⟨4889710657296273856400369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3259807104864182570933579 4889710657296273856400369)
          ·
            refine ⟨3667282992972205392300277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4889710657296273856400369 3667282992972205392300277)
            ·
              refine ⟨343807780591144255528151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3667282992972205392300277 343807780591144255528151)
              ·
                refine ⟨515711670886716383292227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343807780591144255528151 515711670886716383292227)
                ·
                  refine ⟨773567506330074574938341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 515711670886716383292227 773567506330074574938341)
                  ·
                    refine ⟨145043907436888982800939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 773567506330074574938341 145043907436888982800939)
                    ·
                      rfl

theorem cell22_423708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_423708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_423708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_423708 prefixEnd_423708 := by exact prefixLift 423708
  have htrace : WordTrace (prefixWord ++ tailWord_423708) baseStart_423708 baseEnd_423708 := by
    simpa [prefixWord, tailWord_423708, baseEnd_423708] using wordTrace_append hprefix tailTrace_423708
  have hstable : (prefixWord ++ tailWord_423708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423708).length < 2 ^ (prefixWord ++ tailWord_423708).sum := by decide
  have hdescent : baseEnd_423708 < baseStart_423708 := by decide
  rcases family_descends (prefixWord ++ tailWord_423708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423738 : List Nat := [3, 1, 1, 1, 5, 1, 2, 3, 2, 3]
def baseStart_423738 : Nat := 118140960795 + 423738 * 2 ^ 59
def prefixEnd_423738 : Nat := 4983230072969 + 3 ^ 40 * 423738 * 2
def baseEnd_423738 : Nat := 145054177049978904550847

theorem tailTrace_423738 : CollatzResearch.WordTrace tailWord_423738 prefixEnd_423738 145054177049978904550847 := by
  unfold tailWord_423738
  simp only [CollatzResearch.WordTrace]
  refine ⟨3863748634719267383485967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10303329692584713022629245 3863748634719267383485967)
  ·
    refine ⟨5795622952078901075228951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3863748634719267383485967 5795622952078901075228951)
    ·
      refine ⟨8693434428118351612843427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5795622952078901075228951 8693434428118351612843427)
      ·
        refine ⟨13040151642177527419265141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8693434428118351612843427 13040151642177527419265141)
        ·
          refine ⟨1222514216454143195556107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13040151642177527419265141 1222514216454143195556107)
          ·
            refine ⟨1833771324681214793334161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1222514216454143195556107 1833771324681214793334161)
            ·
              refine ⟨1375328493510911095000621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1833771324681214793334161 1375328493510911095000621)
              ·
                refine ⟨515748185066591660625233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1375328493510911095000621 515748185066591660625233)
                ·
                  refine ⟨386811138799943745468925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 515748185066591660625233 386811138799943745468925)
                  ·
                    refine ⟨145054177049978904550847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 386811138799943745468925 145054177049978904550847)
                    ·
                      rfl

theorem cell22_423738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 2, 3].length) (baseStart_423738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_423738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_423738 prefixEnd_423738 := by exact prefixLift 423738
  have htrace : WordTrace (prefixWord ++ tailWord_423738) baseStart_423738 baseEnd_423738 := by
    simpa [prefixWord, tailWord_423738, baseEnd_423738] using wordTrace_append hprefix tailTrace_423738
  have hstable : (prefixWord ++ tailWord_423738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423738).length < 2 ^ (prefixWord ++ tailWord_423738).sum := by decide
  have hdescent : baseEnd_423738 < baseStart_423738 := by decide
  rcases family_descends (prefixWord ++ tailWord_423738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423772 : List Nat := [2, 2, 4, 2, 2, 2, 1, 2, 2, 3]
def baseStart_423772 : Nat := 118140960795 + 423772 * 2 ^ 59
def prefixEnd_423772 : Nat := 4983230072969 + 3 ^ 40 * 423772 * 2
def baseEnd_423772 : Nat := 145065815944814149200743

theorem tailTrace_423772 : CollatzResearch.WordTrace tailWord_423772 prefixEnd_423772 145065815944814149200743 := by
  unfold tailWord_423772
  simp only [CollatzResearch.WordTrace]
  refine ⟨7728117310376946670340785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10304156413835928893787713 7728117310376946670340785)
  ·
    refine ⟨5796087982782710002755589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7728117310376946670340785 5796087982782710002755589)
    ·
      refine ⟨1086766496771758125516673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5796087982782710002755589 1086766496771758125516673)
      ·
        refine ⟨815074872578818594137505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1086766496771758125516673 815074872578818594137505)
        ·
          refine ⟨611306154434113945603129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 815074872578818594137505 611306154434113945603129)
          ·
            refine ⟨458479615825585459202347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 611306154434113945603129 458479615825585459202347)
            ·
              refine ⟨687719423738378188803521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458479615825585459202347 687719423738378188803521)
              ·
                refine ⟨515789567803783641602641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 687719423738378188803521 515789567803783641602641)
                ·
                  refine ⟨386842175852837731201981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 515789567803783641602641 386842175852837731201981)
                  ·
                    refine ⟨145065815944814149200743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 386842175852837731201981 145065815944814149200743)
                    ·
                      rfl

theorem cell22_423772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_423772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_423772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_423772 prefixEnd_423772 := by exact prefixLift 423772
  have htrace : WordTrace (prefixWord ++ tailWord_423772) baseStart_423772 baseEnd_423772 := by
    simpa [prefixWord, tailWord_423772, baseEnd_423772] using wordTrace_append hprefix tailTrace_423772
  have hstable : (prefixWord ++ tailWord_423772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423772).length < 2 ^ (prefixWord ++ tailWord_423772).sum := by decide
  have hdescent : baseEnd_423772 < baseStart_423772 := by decide
  rcases family_descends (prefixWord ++ tailWord_423772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423783 : List Nat := [1, 1, 5, 1, 2, 1, 4, 1, 3, 3]
def baseStart_423783 : Nat := 118140960795 + 423783 * 2 ^ 59
def prefixEnd_423783 : Nat := 4983230072969 + 3 ^ 40 * 423783 * 2
def baseEnd_423783 : Nat := 145069581469613787175709

theorem tailTrace_423783 : CollatzResearch.WordTrace tailWord_423783 prefixEnd_423783 145069581469613787175709 := by
  unfold tailWord_423783
  simp only [CollatzResearch.WordTrace]
  refine ⟨15456635823714042219332003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10304423882476028146221335 15456635823714042219332003)
  ·
    refine ⟨23184953735571063328998005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15456635823714042219332003 23184953735571063328998005)
    ·
      refine ⟨2173589412709787187093563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23184953735571063328998005 2173589412709787187093563)
      ·
        refine ⟨3260384119064680780640345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2173589412709787187093563 3260384119064680780640345)
        ·
          refine ⟨2445288089298510585480259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3260384119064680780640345 2445288089298510585480259)
          ·
            refine ⟨3667932133947765878220389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2445288089298510585480259 3667932133947765878220389)
            ·
              refine ⟨687737275115206102166323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3667932133947765878220389 687737275115206102166323)
              ·
                refine ⟨1031605912672809153249485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 687737275115206102166323 1031605912672809153249485)
                ·
                  refine ⟨386852217252303432468557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1031605912672809153249485 386852217252303432468557)
                  ·
                    refine ⟨145069581469613787175709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 386852217252303432468557 145069581469613787175709)
                    ·
                      rfl

theorem cell22_423783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_423783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_423783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_423783 prefixEnd_423783 := by exact prefixLift 423783
  have htrace : WordTrace (prefixWord ++ tailWord_423783) baseStart_423783 baseEnd_423783 := by
    simpa [prefixWord, tailWord_423783, baseEnd_423783] using wordTrace_append hprefix tailTrace_423783
  have hstable : (prefixWord ++ tailWord_423783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423783).length < 2 ^ (prefixWord ++ tailWord_423783).sum := by decide
  have hdescent : baseEnd_423783 < baseStart_423783 := by decide
  rcases family_descends (prefixWord ++ tailWord_423783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423824 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 10]
def baseStart_423824 : Nat := 118140960795 + 423824 * 2 ^ 59
def prefixEnd_423824 : Nat := 4983230072969 + 3 ^ 40 * 423824 * 2
def baseEnd_423824 : Nat := 48361205535834448966861

theorem tailTrace_423824 : CollatzResearch.WordTrace tailWord_423824 prefixEnd_423824 48361205535834448966861 := by
  unfold tailWord_423824
  simp only [CollatzResearch.WordTrace]
  refine ⟨7729065608282753110787263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10305420811043670814383017 7729065608282753110787263)
  ·
    refine ⟨11593598412424129666180895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7729065608282753110787263 11593598412424129666180895)
    ·
      refine ⟨17390397618636194499271343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11593598412424129666180895 17390397618636194499271343)
      ·
        refine ⟨26085596427954291748907015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17390397618636194499271343 26085596427954291748907015)
        ·
          refine ⟨39128394641931437623360523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26085596427954291748907015 39128394641931437623360523)
          ·
            refine ⟨58692591962897156435040785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39128394641931437623360523 58692591962897156435040785)
            ·
              refine ⟨44019443972172867326280589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58692591962897156435040785 44019443972172867326280589)
              ·
                refine ⟨16507291489564825247355221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44019443972172867326280589 16507291489564825247355221)
                ·
                  refine ⟨48361205535834448966861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 16507291489564825247355221 48361205535834448966861)
                  ·
                    rfl

theorem cell22_423824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 10].length) (baseStart_423824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_423824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_423824 prefixEnd_423824 := by exact prefixLift 423824
  have htrace : WordTrace (prefixWord ++ tailWord_423824) baseStart_423824 baseEnd_423824 := by
    simpa [prefixWord, tailWord_423824, baseEnd_423824] using wordTrace_append hprefix tailTrace_423824
  have hstable : (prefixWord ++ tailWord_423824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423824).length < 2 ^ (prefixWord ++ tailWord_423824).sum := by decide
  have hdescent : baseEnd_423824 < baseStart_423824 := by decide
  rcases family_descends (prefixWord ++ tailWord_423824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_423903 : List Nat := [1, 1, 2, 3, 4, 3, 1, 7]
def baseStart_423903 : Nat := 118140960795 + 423903 * 2 ^ 59
def prefixEnd_423903 : Nat := 4983230072969 + 3 ^ 40 * 423903 * 2
def baseEnd_423903 : Nat := 16123406657997052686149

theorem tailTrace_423903 : CollatzResearch.WordTrace tailWord_423903 prefixEnd_423903 16123406657997052686149 := by
  unfold tailWord_423903
  simp only [CollatzResearch.WordTrace]
  refine ⟨15461012583279302713700363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10307341722186201809133575 15461012583279302713700363)
  ·
    refine ⟨23191518874918954070550545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15461012583279302713700363 23191518874918954070550545)
    ·
      refine ⟨17393639156189215552912909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23191518874918954070550545 17393639156189215552912909)
      ·
        refine ⟨6522614683570955832342341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17393639156189215552912909 6522614683570955832342341)
        ·
          refine ⟨1222990253169554218564189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6522614683570955832342341 1222990253169554218564189)
          ·
            refine ⟨458621344938582831961571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1222990253169554218564189 458621344938582831961571)
            ·
              refine ⟨687932017407874247942357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458621344938582831961571 687932017407874247942357)
              ·
                refine ⟨16123406657997052686149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 687932017407874247942357 16123406657997052686149)
                ·
                  rfl

theorem cell22_423903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 7].length) (baseStart_423903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_423903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_423903 prefixEnd_423903 := by exact prefixLift 423903
  have htrace : WordTrace (prefixWord ++ tailWord_423903) baseStart_423903 baseEnd_423903 := by
    simpa [prefixWord, tailWord_423903, baseEnd_423903] using wordTrace_append hprefix tailTrace_423903
  have hstable : (prefixWord ++ tailWord_423903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_423903).length < 2 ^ (prefixWord ++ tailWord_423903).sum := by decide
  have hdescent : baseEnd_423903 < baseStart_423903 := by decide
  rcases family_descends (prefixWord ++ tailWord_423903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424025 : List Nat := [1, 2, 1, 2, 2, 1, 5, 3, 2, 3]
def baseStart_424025 : Nat := 118140960795 + 424025 * 2 ^ 59
def prefixEnd_424025 : Nat := 4983230072969 + 3 ^ 40 * 424025 * 2
def baseEnd_424025 : Nat := 145152423015205822624967

theorem tailTrace_424025 : CollatzResearch.WordTrace tailWord_424025 prefixEnd_424025 145152423015205822624967 := by
  unfold tailWord_424025
  simp only [CollatzResearch.WordTrace]
  refine ⟨15465462288837317549641529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10310308192558211699761019 15465462288837317549641529)
  ·
    refine ⟨11599096716627988162231147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15465462288837317549641529 11599096716627988162231147)
    ·
      refine ⟨17398645074941982243346721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11599096716627988162231147 17398645074941982243346721)
      ·
        refine ⟨13048983806206486682510041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17398645074941982243346721 13048983806206486682510041)
        ·
          refine ⟨9786737854654865011882531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13048983806206486682510041 9786737854654865011882531)
          ·
            refine ⟨14680106781982297517823797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9786737854654865011882531 14680106781982297517823797)
            ·
              refine ⟨1376260010810840392295981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14680106781982297517823797 1376260010810840392295981)
              ·
                refine ⟨516097504054065147110993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1376260010810840392295981 516097504054065147110993)
                ·
                  refine ⟨387073128040548860333245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 516097504054065147110993 387073128040548860333245)
                  ·
                    refine ⟨145152423015205822624967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 387073128040548860333245 145152423015205822624967)
                    ·
                      rfl

theorem cell22_424025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 2, 3].length) (baseStart_424025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_424025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_424025 prefixEnd_424025 := by exact prefixLift 424025
  have htrace : WordTrace (prefixWord ++ tailWord_424025) baseStart_424025 baseEnd_424025 := by
    simpa [prefixWord, tailWord_424025, baseEnd_424025] using wordTrace_append hprefix tailTrace_424025
  have hstable : (prefixWord ++ tailWord_424025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424025).length < 2 ^ (prefixWord ++ tailWord_424025).sum := by decide
  have hdescent : baseEnd_424025 < baseStart_424025 := by decide
  rcases family_descends (prefixWord ++ tailWord_424025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424029 : List Nat := [1, 4, 4, 1, 1, 3, 1, 2, 1, 4]
def baseStart_424029 : Nat := 118140960795 + 424029 * 2 ^ 59
def prefixEnd_424029 : Nat := 4983230072969 + 3 ^ 40 * 424029 * 2
def baseEnd_424029 : Nat := 145153792296951145524955

theorem tailTrace_424029 : CollatzResearch.WordTrace tailWord_424029 prefixEnd_424029 145153792296951145524955 := by
  unfold tailWord_424029
  simp only [CollatzResearch.WordTrace]
  refine ⟨15465608180822826232787141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10310405453881884155191427 15465608180822826232787141)
  ·
    refine ⟨2899801533904279918647589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15465608180822826232787141 2899801533904279918647589)
    ·
      refine ⟨543712787607052484746423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2899801533904279918647589 543712787607052484746423)
      ·
        refine ⟨815569181410578727119635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543712787607052484746423 815569181410578727119635)
        ·
          refine ⟨1223353772115868090679453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 815569181410578727119635 1223353772115868090679453)
          ·
            refine ⟨458757664543450534004795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1223353772115868090679453 458757664543450534004795)
            ·
              refine ⟨688136496815175801007193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458757664543450534004795 688136496815175801007193)
              ·
                refine ⟨516102372611381850755395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 688136496815175801007193 516102372611381850755395)
                ·
                  refine ⟨774153558917072776133093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 516102372611381850755395 774153558917072776133093)
                  ·
                    refine ⟨145153792296951145524955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 774153558917072776133093 145153792296951145524955)
                    ·
                      rfl

theorem cell22_424029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_424029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_424029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_424029 prefixEnd_424029 := by exact prefixLift 424029
  have htrace : WordTrace (prefixWord ++ tailWord_424029) baseStart_424029 baseEnd_424029 := by
    simpa [prefixWord, tailWord_424029, baseEnd_424029] using wordTrace_append hprefix tailTrace_424029
  have hstable : (prefixWord ++ tailWord_424029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424029).length < 2 ^ (prefixWord ++ tailWord_424029).sum := by decide
  have hdescent : baseEnd_424029 < baseStart_424029 := by decide
  rcases family_descends (prefixWord ++ tailWord_424029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424068 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 1, 8]
def baseStart_424068 : Nat := 118140960795 + 424068 * 2 ^ 59
def prefixEnd_424068 : Nat := 4983230072969 + 3 ^ 40 * 424068 * 2
def baseEnd_424068 : Nat := 145167142793968043799835

theorem tailTrace_424068 : CollatzResearch.WordTrace tailWord_424068 prefixEnd_424068 145167142793968043799835 := by
  unfold tailWord_424068
  simp only [CollatzResearch.WordTrace]
  refine ⟨7733515313840767946728429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10311353751787690595637905 7733515313840767946728429)
  ·
    refine ⟨2900068242690287980023161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7733515313840767946728429 2900068242690287980023161)
    ·
      refine ⟨2175051182017715985017371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2900068242690287980023161 2175051182017715985017371)
      ·
        refine ⟨3262576773026573977526057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2175051182017715985017371 3262576773026573977526057)
        ·
          refine ⟨2446932579769930483144543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3262576773026573977526057 2446932579769930483144543)
          ·
            refine ⟨3670398869654895724716815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2446932579769930483144543 3670398869654895724716815)
            ·
              refine ⟨5505598304482343587075223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3670398869654895724716815 5505598304482343587075223)
              ·
                refine ⟨8258397456723515380612835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5505598304482343587075223 8258397456723515380612835)
                ·
                  refine ⟨12387596185085273070919253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8258397456723515380612835 12387596185085273070919253)
                  ·
                    refine ⟨145167142793968043799835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12387596185085273070919253 145167142793968043799835)
                    ·
                      rfl

theorem cell22_424068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_424068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_424068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_424068 prefixEnd_424068 := by exact prefixLift 424068
  have htrace : WordTrace (prefixWord ++ tailWord_424068) baseStart_424068 baseEnd_424068 := by
    simpa [prefixWord, tailWord_424068, baseEnd_424068] using wordTrace_append hprefix tailTrace_424068
  have hstable : (prefixWord ++ tailWord_424068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424068).length < 2 ^ (prefixWord ++ tailWord_424068).sum := by decide
  have hdescent : baseEnd_424068 < baseStart_424068 := by decide
  rcases family_descends (prefixWord ++ tailWord_424068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424087 : List Nat := [1, 1, 3, 3, 4, 1, 1, 2, 3, 3]
def baseStart_424087 : Nat := 118140960795 + 424087 * 2 ^ 59
def prefixEnd_424087 : Nat := 4983230072969 + 3 ^ 40 * 424087 * 2
def baseEnd_424087 : Nat := 145173646882258327574777

theorem tailTrace_424087 : CollatzResearch.WordTrace tailWord_424087 prefixEnd_424087 145173646882258327574777 := by
  unfold tailWord_424087
  simp only [CollatzResearch.WordTrace]
  refine ⟨15467723614612702138398515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10311815743075134758932343 15467723614612702138398515)
  ·
    refine ⟨23201585421919053207597773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15467723614612702138398515 23201585421919053207597773)
    ·
      refine ⟨8700594533219644952849165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23201585421919053207597773 8700594533219644952849165)
      ·
        refine ⟨3262722949957366857318437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8700594533219644952849165 3262722949957366857318437)
        ·
          refine ⟨611760553117006285747207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3262722949957366857318437 611760553117006285747207)
          ·
            refine ⟨917640829675509428620811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611760553117006285747207 917640829675509428620811)
            ·
              refine ⟨1376461244513264142931217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 917640829675509428620811 1376461244513264142931217)
              ·
                refine ⟨1032345933384948107198413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1376461244513264142931217 1032345933384948107198413)
                ·
                  refine ⟨387129725019355540199405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1032345933384948107198413 387129725019355540199405)
                  ·
                    refine ⟨145173646882258327574777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 387129725019355540199405 145173646882258327574777)
                    ·
                      rfl

theorem cell22_424087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 3, 3].length) (baseStart_424087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_424087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_424087 prefixEnd_424087 := by exact prefixLift 424087
  have htrace : WordTrace (prefixWord ++ tailWord_424087) baseStart_424087 baseEnd_424087 := by
    simpa [prefixWord, tailWord_424087, baseEnd_424087] using wordTrace_append hprefix tailTrace_424087
  have hstable : (prefixWord ++ tailWord_424087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424087).length < 2 ^ (prefixWord ++ tailWord_424087).sum := by decide
  have hdescent : baseEnd_424087 < baseStart_424087 := by decide
  rcases family_descends (prefixWord ++ tailWord_424087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424117 : List Nat := [1, 3, 3, 4, 1, 1, 1, 1, 7]
def baseStart_424117 : Nat := 118140960795 + 424117 * 2 ^ 59
def prefixEnd_424117 : Nat := 4983230072969 + 3 ^ 40 * 424117 * 2
def baseEnd_424117 : Nat := 48394638831782749774895

theorem tailTrace_424117 : CollatzResearch.WordTrace tailWord_424117 prefixEnd_424117 48394638831782749774895 := by
  unfold tailWord_424117
  simp only [CollatzResearch.WordTrace]
  refine ⟨15468817804504017261990605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10312545203002678174660403 15468817804504017261990605)
  ·
    refine ⟨5800806676689006473246477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15468817804504017261990605 5800806676689006473246477)
    ·
      refine ⟨2175302503758377427467429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5800806676689006473246477 2175302503758377427467429)
      ·
        refine ⟨407869219454695767650143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2175302503758377427467429 407869219454695767650143)
        ·
          refine ⟨611803829182043651475215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407869219454695767650143 611803829182043651475215)
          ·
            refine ⟨917705743773065477212823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611803829182043651475215 917705743773065477212823)
            ·
              refine ⟨1376558615659598215819235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 917705743773065477212823 1376558615659598215819235)
              ·
                refine ⟨2064837923489397323728853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1376558615659598215819235 2064837923489397323728853)
                ·
                  refine ⟨48394638831782749774895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2064837923489397323728853 48394638831782749774895)
                  ·
                    rfl

theorem cell22_424117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 7].length) (baseStart_424117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_424117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_424117 prefixEnd_424117 := by exact prefixLift 424117
  have htrace : WordTrace (prefixWord ++ tailWord_424117) baseStart_424117 baseEnd_424117 := by
    simpa [prefixWord, tailWord_424117, baseEnd_424117] using wordTrace_append hprefix tailTrace_424117
  have hstable : (prefixWord ++ tailWord_424117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424117).length < 2 ^ (prefixWord ++ tailWord_424117).sum := by decide
  have hdescent : baseEnd_424117 < baseStart_424117 := by decide
  rcases family_descends (prefixWord ++ tailWord_424117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424160 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 6, 3]
def baseStart_424160 : Nat := 118140960795 + 424160 * 2 ^ 59
def prefixEnd_424160 : Nat := 4983230072969 + 3 ^ 40 * 424160 * 2
def baseEnd_424160 : Nat := 145198636274110470499553

theorem tailTrace_424160 : CollatzResearch.WordTrace tailWord_424160 prefixEnd_424160 145198636274110470499553 := by
  unfold tailWord_424160
  simp only [CollatzResearch.WordTrace]
  refine ⟨7735193071674117802902967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10313590762232157070537289 7735193071674117802902967)
  ·
    refine ⟨11602789607511176704354451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7735193071674117802902967 11602789607511176704354451)
    ·
      refine ⟨17404184411266765056531677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11602789607511176704354451 17404184411266765056531677)
      ·
        refine ⟨6526569154225036896199379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17404184411266765056531677 6526569154225036896199379)
        ·
          refine ⟨9789853731337555344299069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6526569154225036896199379 9789853731337555344299069)
          ·
            refine ⟨3671195149251583254112151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9789853731337555344299069 3671195149251583254112151)
            ·
              refine ⟨5506792723877374881168227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3671195149251583254112151 5506792723877374881168227)
              ·
                refine ⟨8260189085816062321752341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5506792723877374881168227 8260189085816062321752341)
                ·
                  refine ⟨387196363397627921332141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8260189085816062321752341 387196363397627921332141)
                  ·
                    refine ⟨145198636274110470499553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 387196363397627921332141 145198636274110470499553)
                    ·
                      rfl

theorem cell22_424160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 6, 3].length) (baseStart_424160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_424160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_424160 prefixEnd_424160 := by exact prefixLift 424160
  have htrace : WordTrace (prefixWord ++ tailWord_424160) baseStart_424160 baseEnd_424160 := by
    simpa [prefixWord, tailWord_424160, baseEnd_424160] using wordTrace_append hprefix tailTrace_424160
  have hstable : (prefixWord ++ tailWord_424160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424160).length < 2 ^ (prefixWord ++ tailWord_424160).sum := by decide
  have hdescent : baseEnd_424160 < baseStart_424160 := by decide
  rcases family_descends (prefixWord ++ tailWord_424160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424175 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 4, 4]
def baseStart_424175 : Nat := 118140960795 + 424175 * 2 ^ 59
def prefixEnd_424175 : Nat := 4983230072969 + 3 ^ 40 * 424175 * 2
def baseEnd_424175 : Nat := 145203771080655431374507

theorem tailTrace_424175 : CollatzResearch.WordTrace tailWord_424175 prefixEnd_424175 145203771080655431374507 := by
  unfold tailWord_424175
  simp only [CollatzResearch.WordTrace]
  refine ⟨15470933238293893167601979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10313955492195928778401319 15470933238293893167601979)
  ·
    refine ⟨23206399857440839751402969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15470933238293893167601979 23206399857440839751402969)
    ·
      refine ⟨17404799893080629813552227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23206399857440839751402969 17404799893080629813552227)
      ·
        refine ⟨26107199839620944720328341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17404799893080629813552227 26107199839620944720328341)
        ·
          refine ⟨1223774992482231783765391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 26107199839620944720328341 1223774992482231783765391)
          ·
            refine ⟨1835662488723347675648087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1223774992482231783765391 1835662488723347675648087)
            ·
              refine ⟨2753493733085021513472131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1835662488723347675648087 2753493733085021513472131)
              ·
                refine ⟨4130240599627532270208197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2753493733085021513472131 4130240599627532270208197)
                ·
                  refine ⟨774420112430162300664037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4130240599627532270208197 774420112430162300664037)
                  ·
                    refine ⟨145203771080655431374507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 774420112430162300664037 145203771080655431374507)
                    ·
                      rfl

theorem cell22_424175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 4].length) (baseStart_424175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_424175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_424175 prefixEnd_424175 := by exact prefixLift 424175
  have htrace : WordTrace (prefixWord ++ tailWord_424175) baseStart_424175 baseEnd_424175 := by
    simpa [prefixWord, tailWord_424175, baseEnd_424175] using wordTrace_append hprefix tailTrace_424175
  have hstable : (prefixWord ++ tailWord_424175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424175).length < 2 ^ (prefixWord ++ tailWord_424175).sum := by decide
  have hdescent : baseEnd_424175 < baseStart_424175 := by decide
  rcases family_descends (prefixWord ++ tailWord_424175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424250 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 1, 7]
def baseStart_424250 : Nat := 118140960795 + 424250 * 2 ^ 59
def prefixEnd_424250 : Nat := 4983230072969 + 3 ^ 40 * 424250 * 2
def baseEnd_424250 : Nat := 145229445113380235749277

theorem tailTrace_424250 : CollatzResearch.WordTrace tailWord_424250 prefixEnd_424250 145229445113380235749277 := by
  unfold tailWord_424250
  simp only [CollatzResearch.WordTrace]
  refine ⟨3868417178255545244145551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10315779142014787317721469 3868417178255545244145551)
  ·
    refine ⟨5802625767383317866218327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3868417178255545244145551 5802625767383317866218327)
    ·
      refine ⟨8703938651074976799327491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5802625767383317866218327 8703938651074976799327491)
      ·
        refine ⟨13055907976612465198991237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8703938651074976799327491 13055907976612465198991237)
        ·
          refine ⟨2447982745614837224810857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13055907976612465198991237 2447982745614837224810857)
          ·
            refine ⟨1835987059211127918608143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2447982745614837224810857 1835987059211127918608143)
            ·
              refine ⟨2753980588816691877912215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1835987059211127918608143 2753980588816691877912215)
              ·
                refine ⟨4130970883225037816868323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2753980588816691877912215 4130970883225037816868323)
                ·
                  refine ⟨6196456324837556725302485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4130970883225037816868323 6196456324837556725302485)
                  ·
                    refine ⟨145229445113380235749277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6196456324837556725302485 145229445113380235749277)
                    ·
                      rfl

theorem cell22_424250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_424250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_424250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_424250 prefixEnd_424250 := by exact prefixLift 424250
  have htrace : WordTrace (prefixWord ++ tailWord_424250) baseStart_424250 baseEnd_424250 := by
    simpa [prefixWord, tailWord_424250, baseEnd_424250] using wordTrace_append hprefix tailTrace_424250
  have hstable : (prefixWord ++ tailWord_424250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424250).length < 2 ^ (prefixWord ++ tailWord_424250).sum := by decide
  have hdescent : baseEnd_424250 < baseStart_424250 := by decide
  rcases family_descends (prefixWord ++ tailWord_424250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424297 : List Nat := [1, 2, 1, 1, 1, 3, 3, 6, 4]
def baseStart_424297 : Nat := 118140960795 + 424297 * 2 ^ 59
def prefixEnd_424297 : Nat := 4983230072969 + 3 ^ 40 * 424297 * 2
def baseEnd_424297 : Nat := 48415178057962593274711

theorem tailTrace_424297 : CollatzResearch.WordTrace tailWord_424297 prefixEnd_424297 48415178057962593274711 := by
  unfold tailWord_424297
  simp only [CollatzResearch.WordTrace]
  refine ⟨15475382943851908003543145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10316921962567938669028763 15475382943851908003543145)
  ·
    refine ⟨11606537207888931002657359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15475382943851908003543145 11606537207888931002657359)
    ·
      refine ⟨17409805811833396503986039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11606537207888931002657359 17409805811833396503986039)
      ·
        refine ⟨26114708717750094755979059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17409805811833396503986039 26114708717750094755979059)
        ·
          refine ⟨39172063076625142133968589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26114708717750094755979059 39172063076625142133968589)
          ·
            refine ⟨14689523653734428300238221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39172063076625142133968589 14689523653734428300238221)
            ·
              refine ⟨5508571370150410612589333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14689523653734428300238221 5508571370150410612589333)
              ·
                refine ⟨258214282975800497465125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5508571370150410612589333 258214282975800497465125)
                ·
                  refine ⟨48415178057962593274711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 258214282975800497465125 48415178057962593274711)
                  ·
                    rfl

theorem cell22_424297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 6, 4].length) (baseStart_424297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_424297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_424297 prefixEnd_424297 := by exact prefixLift 424297
  have htrace : WordTrace (prefixWord ++ tailWord_424297) baseStart_424297 baseEnd_424297 := by
    simpa [prefixWord, tailWord_424297, baseEnd_424297] using wordTrace_append hprefix tailTrace_424297
  have hstable : (prefixWord ++ tailWord_424297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424297).length < 2 ^ (prefixWord ++ tailWord_424297).sum := by decide
  have hdescent : baseEnd_424297 < baseStart_424297 := by decide
  rcases family_descends (prefixWord ++ tailWord_424297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424327 : List Nat := [1, 1, 4, 2, 2, 1, 2, 3, 2, 4]
def baseStart_424327 : Nat := 118140960795 + 424327 * 2 ^ 59
def prefixEnd_424327 : Nat := 4983230072969 + 3 ^ 40 * 424327 * 2
def baseEnd_424327 : Nat := 145255803786977701574041

theorem tailTrace_424327 : CollatzResearch.WordTrace tailWord_424327 prefixEnd_424327 145255803786977701574041 := by
  unfold tailWord_424327
  simp only [CollatzResearch.WordTrace]
  refine ⟨15476477133743223127135235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10317651422495482084756823 15476477133743223127135235)
  ·
    refine ⟨23214715700614834690702853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15476477133743223127135235 23214715700614834690702853)
    ·
      refine ⟨4352759193865281504506785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23214715700614834690702853 4352759193865281504506785)
      ·
        refine ⟨3264569395398961128380089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4352759193865281504506785 3264569395398961128380089)
        ·
          refine ⟨2448427046549220846285067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3264569395398961128380089 2448427046549220846285067)
          ·
            refine ⟨3672640569823831269427601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2448427046549220846285067 3672640569823831269427601)
            ·
              refine ⟨2754480427367873452070701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3672640569823831269427601 2754480427367873452070701)
              ·
                refine ⟨1032930160262952544526513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2754480427367873452070701 1032930160262952544526513)
                ·
                  refine ⟨774697620197214408394885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1032930160262952544526513 774697620197214408394885)
                  ·
                    refine ⟨145255803786977701574041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 774697620197214408394885 145255803786977701574041)
                    ·
                      rfl

theorem cell22_424327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_424327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_424327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_424327 prefixEnd_424327 := by exact prefixLift 424327
  have htrace : WordTrace (prefixWord ++ tailWord_424327) baseStart_424327 baseEnd_424327 := by
    simpa [prefixWord, tailWord_424327, baseEnd_424327] using wordTrace_append hprefix tailTrace_424327
  have hstable : (prefixWord ++ tailWord_424327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424327).length < 2 ^ (prefixWord ++ tailWord_424327).sum := by decide
  have hdescent : baseEnd_424327 < baseStart_424327 := by decide
  rcases family_descends (prefixWord ++ tailWord_424327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424344 : List Nat := [2, 1, 2, 5, 1, 2, 1, 2, 2, 4]
def baseStart_424344 : Nat := 118140960795 + 424344 * 2 ^ 59
def prefixEnd_424344 : Nat := 4983230072969 + 3 ^ 40 * 424344 * 2
def baseEnd_424344 : Nat := 145261623234395323898989

theorem tailTrace_424344 : CollatzResearch.WordTrace tailWord_424344 prefixEnd_424344 145261623234395323898989 := by
  unfold tailWord_424344
  simp only [CollatzResearch.WordTrace]
  refine ⟨7738548587340817515252043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10318064783121090020336057 7738548587340817515252043)
  ·
    refine ⟨11607822881011226272878065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7738548587340817515252043 11607822881011226272878065)
    ·
      refine ⟨8705867160758419704658549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11607822881011226272878065 8705867160758419704658549)
      ·
        refine ⟨816175046321101847311739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8705867160758419704658549 816175046321101847311739)
        ·
          refine ⟨1224262569481652770967609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 816175046321101847311739 1224262569481652770967609)
          ·
            refine ⟨918196927111239578225707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1224262569481652770967609 918196927111239578225707)
            ·
              refine ⟨1377295390666859367338561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 918196927111239578225707 1377295390666859367338561)
              ·
                refine ⟨1032971543000144525503921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1377295390666859367338561 1032971543000144525503921)
                ·
                  refine ⟨774728657250108394127941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1032971543000144525503921 774728657250108394127941)
                  ·
                    refine ⟨145261623234395323898989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 774728657250108394127941 145261623234395323898989)
                    ·
                      rfl

theorem cell22_424344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_424344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_424344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_424344 prefixEnd_424344 := by exact prefixLift 424344
  have htrace : WordTrace (prefixWord ++ tailWord_424344) baseStart_424344 baseEnd_424344 := by
    simpa [prefixWord, tailWord_424344, baseEnd_424344] using wordTrace_append hprefix tailTrace_424344
  have hstable : (prefixWord ++ tailWord_424344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424344).length < 2 ^ (prefixWord ++ tailWord_424344).sum := by decide
  have hdescent : baseEnd_424344 < baseStart_424344 := by decide
  rcases family_descends (prefixWord ++ tailWord_424344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424404 : List Nat := [2, 4, 1, 2, 2, 1, 1, 4, 5]
def baseStart_424404 : Nat := 118140960795 + 424404 * 2 ^ 59
def prefixEnd_424404 : Nat := 4983230072969 + 3 ^ 40 * 424404 * 2
def baseEnd_424404 : Nat := 48427387486858389132935

theorem tailTrace_424404 : CollatzResearch.WordTrace tailWord_424404 prefixEnd_424404 48427387486858389132935 := by
  unfold tailWord_424404
  simp only [CollatzResearch.WordTrace]
  refine ⟨7739642777232132638844133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10319523702976176851792177 7739642777232132638844133)
  ·
    refine ⟨1451183020731024869783275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7739642777232132638844133 1451183020731024869783275)
    ·
      refine ⟨2176774531096537304674913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1451183020731024869783275 2176774531096537304674913)
      ·
        refine ⟨1632580898322402978506185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2176774531096537304674913 1632580898322402978506185)
        ·
          refine ⟨1224435673741802233879639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1632580898322402978506185 1224435673741802233879639)
          ·
            refine ⟨1836653510612703350819459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1224435673741802233879639 1836653510612703350819459)
            ·
              refine ⟨2754980265919055026229189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1836653510612703350819459 2754980265919055026229189)
              ·
                refine ⟨516558799859822817417973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2754980265919055026229189 516558799859822817417973)
                ·
                  refine ⟨48427387486858389132935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 516558799859822817417973 48427387486858389132935)
                  ·
                    rfl

theorem cell22_424404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_424404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_424404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_424404 prefixEnd_424404 := by exact prefixLift 424404
  have htrace : WordTrace (prefixWord ++ tailWord_424404) baseStart_424404 baseEnd_424404 := by
    simpa [prefixWord, tailWord_424404, baseEnd_424404] using wordTrace_append hprefix tailTrace_424404
  have hstable : (prefixWord ++ tailWord_424404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424404).length < 2 ^ (prefixWord ++ tailWord_424404).sum := by decide
  have hdescent : baseEnd_424404 < baseStart_424404 := by decide
  rcases family_descends (prefixWord ++ tailWord_424404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424417 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 5, 4]
def baseStart_424417 : Nat := 118140960795 + 424417 * 2 ^ 59
def prefixEnd_424417 : Nat := 4983230072969 + 3 ^ 40 * 424417 * 2
def baseEnd_424417 : Nat := 145286612626247466823765

theorem tailTrace_424417 : CollatzResearch.WordTrace tailWord_424417 prefixEnd_424417 145286612626247466823765 := by
  unfold tailWord_424417
  simp only [CollatzResearch.WordTrace]
  refine ⟨15479759703417168497911505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10319839802278112331941003 15479759703417168497911505)
  ·
    refine ⟨11609819777562876373433629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15479759703417168497911505 11609819777562876373433629)
    ·
      refine ⟨4353682416586078640037611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11609819777562876373433629 4353682416586078640037611)
      ·
        refine ⟨6530523624879117960056417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4353682416586078640037611 6530523624879117960056417)
        ·
          refine ⟨4897892718659338470042313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6530523624879117960056417 4897892718659338470042313)
          ·
            refine ⟨3673419538994503852531735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4897892718659338470042313 3673419538994503852531735)
            ·
              refine ⟨5510129308491755778797603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3673419538994503852531735 5510129308491755778797603)
              ·
                refine ⟨8265193962737633668196405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5510129308491755778797603 8265193962737633668196405)
                ·
                  refine ⟨774861934006653156393413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8265193962737633668196405 774861934006653156393413)
                  ·
                    refine ⟨145286612626247466823765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 774861934006653156393413 145286612626247466823765)
                    ·
                      rfl

theorem cell22_424417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_424417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_424417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_424417 prefixEnd_424417 := by exact prefixLift 424417
  have htrace : WordTrace (prefixWord ++ tailWord_424417) baseStart_424417 baseEnd_424417 := by
    simpa [prefixWord, tailWord_424417, baseEnd_424417] using wordTrace_append hprefix tailTrace_424417
  have hstable : (prefixWord ++ tailWord_424417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424417).length < 2 ^ (prefixWord ++ tailWord_424417).sum := by decide
  have hdescent : baseEnd_424417 < baseStart_424417 := by decide
  rcases family_descends (prefixWord ++ tailWord_424417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424419 : List Nat := [1, 1, 1, 6, 3, 1, 1, 1, 2, 5]
def baseStart_424419 : Nat := 118140960795 + 424419 * 2 ^ 59
def prefixEnd_424419 : Nat := 4983230072969 + 3 ^ 40 * 424419 * 2
def baseEnd_424419 : Nat := 145287297267120128273759

theorem tailTrace_424419 : CollatzResearch.WordTrace tailWord_424419 prefixEnd_424419 145287297267120128273759 := by
  unfold tailWord_424419
  simp only [CollatzResearch.WordTrace]
  refine ⟨15479832649409922839484311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10319888432939948559656207 15479832649409922839484311)
  ·
    refine ⟨23219748974114884259226467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15479832649409922839484311 23219748974114884259226467)
    ·
      refine ⟨34829623461172326388839701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23219748974114884259226467 34829623461172326388839701)
      ·
        refine ⟨1632638599742452799476861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34829623461172326388839701 1632638599742452799476861)
        ·
          refine ⟨612239474903419799803823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1632638599742452799476861 612239474903419799803823)
          ·
            refine ⟨918359212355129699705735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612239474903419799803823 918359212355129699705735)
            ·
              refine ⟨1377538818532694549558603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 918359212355129699705735 1377538818532694549558603)
              ·
                refine ⟨2066308227799041824337905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1377538818532694549558603 2066308227799041824337905)
                ·
                  refine ⟨1549731170849281368253429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2066308227799041824337905 1549731170849281368253429)
                  ·
                    refine ⟨145287297267120128273759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1549731170849281368253429 145287297267120128273759)
                    ·
                      rfl

theorem cell22_424419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 5].length) (baseStart_424419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_424419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_424419 prefixEnd_424419 := by exact prefixLift 424419
  have htrace : WordTrace (prefixWord ++ tailWord_424419) baseStart_424419 baseEnd_424419 := by
    simpa [prefixWord, tailWord_424419, baseEnd_424419] using wordTrace_append hprefix tailTrace_424419
  have hstable : (prefixWord ++ tailWord_424419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424419).length < 2 ^ (prefixWord ++ tailWord_424419).sum := by decide
  have hdescent : baseEnd_424419 < baseStart_424419 := by decide
  rcases family_descends (prefixWord ++ tailWord_424419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424432 : List Nat := [2, 1, 1, 1, 3, 3, 3, 2, 6]
def baseStart_424432 : Nat := 118140960795 + 424432 * 2 ^ 59
def prefixEnd_424432 : Nat := 4983230072969 + 3 ^ 40 * 424432 * 2
def baseEnd_424432 : Nat := 48430582477597475899573

theorem tailTrace_424432 : CollatzResearch.WordTrace tailWord_424432 prefixEnd_424432 48430582477597475899573 := by
  unfold tailWord_424432
  simp only [CollatzResearch.WordTrace]
  refine ⟨7740153399181413029853775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10320204532241884039805033 7740153399181413029853775)
  ·
    refine ⟨11610230098772119544780663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7740153399181413029853775 11610230098772119544780663)
    ·
      refine ⟨17415345148158179317170995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11610230098772119544780663 17415345148158179317170995)
      ·
        refine ⟨26123017722237268975756493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17415345148158179317170995 26123017722237268975756493)
        ·
          refine ⟨9796131645838975865908685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26123017722237268975756493 9796131645838975865908685)
          ·
            refine ⟨3673549367189615949715757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9796131645838975865908685 3673549367189615949715757)
            ·
              refine ⟨1377581012696105981143409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3673549367189615949715757 1377581012696105981143409)
              ·
                refine ⟨1033185759522079485857557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1377581012696105981143409 1033185759522079485857557)
                ·
                  refine ⟨48430582477597475899573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1033185759522079485857557 48430582477597475899573)
                  ·
                    rfl

theorem cell22_424432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 6].length) (baseStart_424432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_424432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_424432 prefixEnd_424432 := by exact prefixLift 424432
  have htrace : WordTrace (prefixWord ++ tailWord_424432) baseStart_424432 baseEnd_424432 := by
    simpa [prefixWord, tailWord_424432, baseEnd_424432] using wordTrace_append hprefix tailTrace_424432
  have hstable : (prefixWord ++ tailWord_424432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424432).length < 2 ^ (prefixWord ++ tailWord_424432).sum := by decide
  have hdescent : baseEnd_424432 < baseStart_424432 := by decide
  rcases family_descends (prefixWord ++ tailWord_424432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424447 : List Nat := [1, 1, 2, 2, 1, 2, 3, 4, 1, 5]
def baseStart_424447 : Nat := 118140960795 + 424447 * 2 ^ 59
def prefixEnd_424447 : Nat := 4983230072969 + 3 ^ 40 * 424447 * 2
def baseEnd_424447 : Nat := 145296882239337388573673

theorem tailTrace_424447 : CollatzResearch.WordTrace tailWord_424447 prefixEnd_424447 145296882239337388573673 := by
  unfold tailWord_424447
  simp only [CollatzResearch.WordTrace]
  refine ⟨15480853893308483621503595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10320569262205655747669063 15480853893308483621503595)
  ·
    refine ⟨23221280839962725432255393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15480853893308483621503595 23221280839962725432255393)
    ·
      refine ⟨17415960629972044074191545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23221280839962725432255393 17415960629972044074191545)
      ·
        refine ⟨13061970472479033055643659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17415960629972044074191545 13061970472479033055643659)
        ·
          refine ⟨19592955708718549583465489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13061970472479033055643659 19592955708718549583465489)
          ·
            refine ⟨14694716781538912187599117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19592955708718549583465489 14694716781538912187599117)
            ·
              refine ⟨5510518793077092070349669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14694716781538912187599117 5510518793077092070349669)
              ·
                refine ⟨1033222273701954763190563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5510518793077092070349669 1033222273701954763190563)
                ·
                  refine ⟨1549833410552932144785845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1033222273701954763190563 1549833410552932144785845)
                  ·
                    refine ⟨145296882239337388573673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1549833410552932144785845 145296882239337388573673)
                    ·
                      rfl

theorem cell22_424447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 5].length) (baseStart_424447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_424447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_424447 prefixEnd_424447 := by exact prefixLift 424447
  have htrace : WordTrace (prefixWord ++ tailWord_424447) baseStart_424447 baseEnd_424447 := by
    simpa [prefixWord, tailWord_424447, baseEnd_424447] using wordTrace_append hprefix tailTrace_424447
  have hstable : (prefixWord ++ tailWord_424447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424447).length < 2 ^ (prefixWord ++ tailWord_424447).sum := by decide
  have hdescent : baseEnd_424447 < baseStart_424447 := by decide
  rcases family_descends (prefixWord ++ tailWord_424447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424526 : List Nat := [4, 1, 1, 1, 1, 2, 5, 1, 3, 3]
def baseStart_424526 : Nat := 118140960795 + 424526 * 2 ^ 59
def prefixEnd_424526 : Nat := 4983230072969 + 3 ^ 40 * 424526 * 2
def baseEnd_424526 : Nat := 145323925553807515848431

theorem tailTrace_424526 : CollatzResearch.WordTrace tailWord_424526 prefixEnd_424526 145323925553807515848431 := by
  unfold tailWord_424526
  simp only [CollatzResearch.WordTrace]
  refine ⟨1935466907502785014203679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10322490173348186742419621 1935466907502785014203679)
  ·
    refine ⟨2903200361254177521305519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1935466907502785014203679 2903200361254177521305519)
    ·
      refine ⟨4354800541881266281958279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2903200361254177521305519 4354800541881266281958279)
      ·
        refine ⟨6532200812821899422937419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4354800541881266281958279 6532200812821899422937419)
        ·
          refine ⟨9798301219232849134406129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6532200812821899422937419 9798301219232849134406129)
          ·
            refine ⟨7348725914424636850804597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9798301219232849134406129 7348725914424636850804597)
            ·
              refine ⟨688943054477309704762931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7348725914424636850804597 688943054477309704762931)
              ·
                refine ⟨1033414581715964557144397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 688943054477309704762931 1033414581715964557144397)
                ·
                  refine ⟨387530468143486708929149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1033414581715964557144397 387530468143486708929149)
                  ·
                    refine ⟨145323925553807515848431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 387530468143486708929149 145323925553807515848431)
                    ·
                      rfl

theorem cell22_424526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_424526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_424526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_424526 prefixEnd_424526 := by exact prefixLift 424526
  have htrace : WordTrace (prefixWord ++ tailWord_424526) baseStart_424526 baseEnd_424526 := by
    simpa [prefixWord, tailWord_424526, baseEnd_424526] using wordTrace_append hprefix tailTrace_424526
  have hstable : (prefixWord ++ tailWord_424526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424526).length < 2 ^ (prefixWord ++ tailWord_424526).sum := by decide
  have hdescent : baseEnd_424526 < baseStart_424526 := by decide
  rcases family_descends (prefixWord ++ tailWord_424526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424650 : List Nat := [3, 1, 2, 1, 4, 2, 3, 1, 2, 3]
def baseStart_424650 : Nat := 118140960795 + 424650 * 2 ^ 59
def prefixEnd_424650 : Nat := 4983230072969 + 3 ^ 40 * 424650 * 2
def baseEnd_424650 : Nat := 145366373287912525748051

theorem tailTrace_424650 : CollatzResearch.WordTrace tailWord_424650 prefixEnd_424650 145366373287912525748051 := by
  unfold tailWord_424650
  simp only [CollatzResearch.WordTrace]
  refine ⟨3872064477893262322785851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10325505274382032860762269 3872064477893262322785851)
  ·
    refine ⟨5808096716839893484178777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3872064477893262322785851 5808096716839893484178777)
    ·
      refine ⟨4356072537629920113134083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5808096716839893484178777 4356072537629920113134083)
      ·
        refine ⟨6534108806444880169701125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4356072537629920113134083 6534108806444880169701125)
        ·
          refine ⟨1225145401208415031818961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6534108806444880169701125 1225145401208415031818961)
          ·
            refine ⟨918859050906311273864221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1225145401208415031818961 918859050906311273864221)
            ·
              refine ⟨344572144089866727699083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 918859050906311273864221 344572144089866727699083)
              ·
                refine ⟨516858216134800091548625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 344572144089866727699083 516858216134800091548625)
                ·
                  refine ⟨387643662101100068661469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 516858216134800091548625 387643662101100068661469)
                  ·
                    refine ⟨145366373287912525748051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 387643662101100068661469 145366373287912525748051)
                    ·
                      rfl

theorem cell22_424650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_424650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_424650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_424650 prefixEnd_424650 := by exact prefixLift 424650
  have htrace : WordTrace (prefixWord ++ tailWord_424650) baseStart_424650 baseEnd_424650 := by
    simpa [prefixWord, tailWord_424650, baseEnd_424650] using wordTrace_append hprefix tailTrace_424650
  have hstable : (prefixWord ++ tailWord_424650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424650).length < 2 ^ (prefixWord ++ tailWord_424650).sum := by decide
  have hdescent : baseEnd_424650 < baseStart_424650 := by decide
  rcases family_descends (prefixWord ++ tailWord_424650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424719 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 8]
def baseStart_424719 : Nat := 118140960795 + 424719 * 2 ^ 59
def prefixEnd_424719 : Nat := 4983230072969 + 3 ^ 40 * 424719 * 2
def baseEnd_424719 : Nat := 48463331132673115257613

theorem tailTrace_424719 : CollatzResearch.WordTrace tailWord_424719 prefixEnd_424719 48463331132673115257613 := by
  unfold tailWord_424719
  simp only [CollatzResearch.WordTrace]
  refine ⟨15490774548323074075405211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10327183032215382716936807 15490774548323074075405211)
  ·
    refine ⟨23236161822484611113107817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15490774548323074075405211 23236161822484611113107817)
    ·
      refine ⟨17427121366863458334830863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23236161822484611113107817 17427121366863458334830863)
      ·
        refine ⟨26140682050295187502246295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17427121366863458334830863 26140682050295187502246295)
        ·
          refine ⟨39211023075442781253369443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26140682050295187502246295 39211023075442781253369443)
          ·
            refine ⟨58816534613164171880054165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39211023075442781253369443 58816534613164171880054165)
            ·
              refine ⟨2757025059992070556877539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58816534613164171880054165 2757025059992070556877539)
              ·
                refine ⟨4135537589988105835316309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2757025059992070556877539 4135537589988105835316309)
                ·
                  refine ⟨48463331132673115257613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4135537589988105835316309 48463331132673115257613)
                  ·
                    rfl

theorem cell22_424719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 8].length) (baseStart_424719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_424719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_424719 prefixEnd_424719 := by exact prefixLift 424719
  have htrace : WordTrace (prefixWord ++ tailWord_424719) baseStart_424719 baseEnd_424719 := by
    simpa [prefixWord, tailWord_424719, baseEnd_424719] using wordTrace_append hprefix tailTrace_424719
  have hstable : (prefixWord ++ tailWord_424719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424719).length < 2 ^ (prefixWord ++ tailWord_424719).sum := by decide
  have hdescent : baseEnd_424719 < baseStart_424719 := by decide
  rcases family_descends (prefixWord ++ tailWord_424719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424746 : List Nat := [3, 1, 4, 3, 1, 2, 2, 2, 1, 3]
def baseStart_424746 : Nat := 118140960795 + 424746 * 2 ^ 59
def prefixEnd_424746 : Nat := 4983230072969 + 3 ^ 40 * 424746 * 2
def baseEnd_424746 : Nat := 145399236049800275347757

theorem tailTrace_424746 : CollatzResearch.WordTrace tailWord_424746 prefixEnd_424746 145399236049800275347757 := by
  unfold tailWord_424746
  simp only [CollatzResearch.WordTrace]
  refine ⟨3872939829806314421659523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10327839546150171791092061 3872939829806314421659523)
  ·
    refine ⟨5809409744709471632489285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3872939829806314421659523 5809409744709471632489285)
    ·
      refine ⟨1089264327133025931091741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5809409744709471632489285 1089264327133025931091741)
      ·
        refine ⟨408474122674884724159403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1089264327133025931091741 408474122674884724159403)
        ·
          refine ⟨612711184012327086239105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408474122674884724159403 612711184012327086239105)
          ·
            refine ⟨459533388009245314679329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 612711184012327086239105 459533388009245314679329)
            ·
              refine ⟨344650041006933986009497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 459533388009245314679329 344650041006933986009497)
              ·
                refine ⟨258487530755200489507123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 344650041006933986009497 258487530755200489507123)
                ·
                  refine ⟨387731296132800734260685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258487530755200489507123 387731296132800734260685)
                  ·
                    refine ⟨145399236049800275347757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 387731296132800734260685 145399236049800275347757)
                    ·
                      rfl

theorem cell22_424746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_424746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_424746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_424746 prefixEnd_424746 := by exact prefixLift 424746
  have htrace : WordTrace (prefixWord ++ tailWord_424746) baseStart_424746 baseEnd_424746 := by
    simpa [prefixWord, tailWord_424746, baseEnd_424746] using wordTrace_append hprefix tailTrace_424746
  have hstable : (prefixWord ++ tailWord_424746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424746).length < 2 ^ (prefixWord ++ tailWord_424746).sum := by decide
  have hdescent : baseEnd_424746 < baseStart_424746 := by decide
  rcases family_descends (prefixWord ++ tailWord_424746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424753 : List Nat := [1, 2, 2, 3, 2, 1, 3, 4, 4]
def baseStart_424753 : Nat := 118140960795 + 424753 * 2 ^ 59
def prefixEnd_424753 : Nat := 4983230072969 + 3 ^ 40 * 424753 * 2
def baseEnd_424753 : Nat := 48467210764284863474245

theorem tailTrace_424753 : CollatzResearch.WordTrace tailWord_424753 prefixEnd_424753 48467210764284863474245 := by
  unfold tailWord_424753
  simp only [CollatzResearch.WordTrace]
  refine ⟨15492014630199897882142913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10328009753466598588095275 15492014630199897882142913)
  ·
    refine ⟨11619010972649923411607185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15492014630199897882142913 11619010972649923411607185)
    ·
      refine ⟨8714258229487442558705389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11619010972649923411607185 8714258229487442558705389)
      ·
        refine ⟨3267846836057790959514521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8714258229487442558705389 3267846836057790959514521)
        ·
          refine ⟨2450885127043343219635891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3267846836057790959514521 2450885127043343219635891)
          ·
            refine ⟨3676327690565014829453837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2450885127043343219635891 3676327690565014829453837)
            ·
              refine ⟨1378622883961880561045189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3676327690565014829453837 1378622883961880561045189)
              ·
                refine ⟨258491790742852605195973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1378622883961880561045189 258491790742852605195973)
                ·
                  refine ⟨48467210764284863474245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 258491790742852605195973 48467210764284863474245)
                  ·
                    rfl

theorem cell22_424753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 4, 4].length) (baseStart_424753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_424753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_424753 prefixEnd_424753 := by exact prefixLift 424753
  have htrace : WordTrace (prefixWord ++ tailWord_424753) baseStart_424753 baseEnd_424753 := by
    simpa [prefixWord, tailWord_424753, baseEnd_424753] using wordTrace_append hprefix tailTrace_424753
  have hstable : (prefixWord ++ tailWord_424753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424753).length < 2 ^ (prefixWord ++ tailWord_424753).sum := by decide
  have hdescent : baseEnd_424753 < baseStart_424753 := by decide
  rcases family_descends (prefixWord ++ tailWord_424753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424877 : List Nat := [1, 5, 2, 3, 1, 1, 1, 3, 5]
def baseStart_424877 : Nat := 118140960795 + 424877 * 2 ^ 59
def prefixEnd_424877 : Nat := 4983230072969 + 3 ^ 40 * 424877 * 2
def baseEnd_424877 : Nat := 48481360008986533440785

theorem tailTrace_424877 : CollatzResearch.WordTrace tailWord_424877 prefixEnd_424877 48481360008986533440785 := by
  unfold tailWord_424877
  simp only [CollatzResearch.WordTrace]
  refine ⟨15496537281750667059656885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10331024854500444706437923 15496537281750667059656885)
  ·
    refine ⟨1452800370164125036842833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15496537281750667059656885 1452800370164125036842833)
    ·
      refine ⟨1089600277623093777632125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1452800370164125036842833 1089600277623093777632125)
      ·
        refine ⟨408600104108660166612047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1089600277623093777632125 408600104108660166612047)
        ·
          refine ⟨612900156162990249918071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408600104108660166612047 612900156162990249918071)
          ·
            refine ⟨919350234244485374877107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612900156162990249918071 919350234244485374877107)
            ·
              refine ⟨1379025351366728062315661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 919350234244485374877107 1379025351366728062315661)
              ·
                refine ⟨517134506762523023368373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1379025351366728062315661 517134506762523023368373)
                ·
                  refine ⟨48481360008986533440785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 517134506762523023368373 48481360008986533440785)
                  ·
                    rfl

theorem cell22_424877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_424877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_424877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_424877 prefixEnd_424877 := by exact prefixLift 424877
  have htrace : WordTrace (prefixWord ++ tailWord_424877) baseStart_424877 baseEnd_424877 := by
    simpa [prefixWord, tailWord_424877, baseEnd_424877] using wordTrace_append hprefix tailTrace_424877
  have hstable : (prefixWord ++ tailWord_424877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424877).length < 2 ^ (prefixWord ++ tailWord_424877).sum := by decide
  have hdescent : baseEnd_424877 < baseStart_424877 := by decide
  rcases family_descends (prefixWord ++ tailWord_424877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424901 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 5, 6]
def baseStart_424901 : Nat := 118140960795 + 424901 * 2 ^ 59
def prefixEnd_424901 : Nat := 4983230072969 + 3 ^ 40 * 424901 * 2
def baseEnd_424901 : Nat := 145452295717431537722281

theorem tailTrace_424901 : CollatzResearch.WordTrace tailWord_424901 prefixEnd_424901 145452295717431537722281 := by
  unfold tailWord_424901
  simp only [CollatzResearch.WordTrace]
  refine ⟨15497412633663719158530557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10331608422442479439020371 15497412633663719158530557)
  ·
    refine ⟨5811529737623894684448959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15497412633663719158530557 5811529737623894684448959)
    ·
      refine ⟨8717294606435842026673439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5811529737623894684448959 8717294606435842026673439)
      ·
        refine ⟨13075941909653763040010159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8717294606435842026673439 13075941909653763040010159)
        ·
          refine ⟨19613912864480644560015239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13075941909653763040010159 19613912864480644560015239)
          ·
            refine ⟨29420869296720966840022859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19613912864480644560015239 29420869296720966840022859)
            ·
              refine ⟨44131303945081450260034289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29420869296720966840022859 44131303945081450260034289)
              ·
                refine ⟨33098477958811087695025717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44131303945081450260034289 33098477958811087695025717)
                ·
                  refine ⟨3102982308638539471408661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33098477958811087695025717 3102982308638539471408661)
                  ·
                    refine ⟨145452295717431537722281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3102982308638539471408661 145452295717431537722281)
                    ·
                      rfl

theorem cell22_424901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_424901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_424901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_424901 prefixEnd_424901 := by exact prefixLift 424901
  have htrace : WordTrace (prefixWord ++ tailWord_424901) baseStart_424901 baseEnd_424901 := by
    simpa [prefixWord, tailWord_424901, baseEnd_424901] using wordTrace_append hprefix tailTrace_424901
  have hstable : (prefixWord ++ tailWord_424901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424901).length < 2 ^ (prefixWord ++ tailWord_424901).sum := by decide
  have hdescent : baseEnd_424901 < baseStart_424901 := by decide
  rcases family_descends (prefixWord ++ tailWord_424901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424903 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 6, 3]
def baseStart_424903 : Nat := 118140960795 + 424903 * 2 ^ 59
def prefixEnd_424903 : Nat := 4983230072969 + 3 ^ 40 * 424903 * 2
def baseEnd_424903 : Nat := 145452980358304199172275

theorem tailTrace_424903 : CollatzResearch.WordTrace tailWord_424903 prefixEnd_424903 145452980358304199172275 := by
  unfold tailWord_424903
  simp only [CollatzResearch.WordTrace]
  refine ⟨15497485579656473500103363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10331657053104315666735575 15497485579656473500103363)
  ·
    refine ⟨23246228369484710250155045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15497485579656473500103363 23246228369484710250155045)
    ·
      refine ⟨4358667819278383171904071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23246228369484710250155045 4358667819278383171904071)
      ·
        refine ⟨6538001728917574757856107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4358667819278383171904071 6538001728917574757856107)
        ·
          refine ⟨9807002593376362136784161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6538001728917574757856107 9807002593376362136784161)
          ·
            refine ⟨7355251945032271602588121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9807002593376362136784161 7355251945032271602588121)
            ·
              refine ⟨5516438958774203701941091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7355251945032271602588121 5516438958774203701941091)
              ·
                refine ⟨8274658438161305552911637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5516438958774203701941091 8274658438161305552911637)
                ·
                  refine ⟨387874614288811197792733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8274658438161305552911637 387874614288811197792733)
                  ·
                    refine ⟨145452980358304199172275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 387874614288811197792733 145452980358304199172275)
                    ·
                      rfl

theorem cell22_424903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_424903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_424903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_424903 prefixEnd_424903 := by exact prefixLift 424903
  have htrace : WordTrace (prefixWord ++ tailWord_424903) baseStart_424903 baseEnd_424903 := by
    simpa [prefixWord, tailWord_424903, baseEnd_424903] using wordTrace_append hprefix tailTrace_424903
  have hstable : (prefixWord ++ tailWord_424903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424903).length < 2 ^ (prefixWord ++ tailWord_424903).sum := by decide
  have hdescent : baseEnd_424903 < baseStart_424903 := by decide
  rcases family_descends (prefixWord ++ tailWord_424903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424920 : List Nat := [2, 1, 2, 2, 2, 3, 1, 4, 2, 3]
def baseStart_424920 : Nat := 118140960795 + 424920 * 2 ^ 59
def prefixEnd_424920 : Nat := 4983230072969 + 3 ^ 40 * 424920 * 2
def baseEnd_424920 : Nat := 145458799805721821497223

theorem tailTrace_424920 : CollatzResearch.WordTrace tailWord_424920 prefixEnd_424920 145458799805721821497223 := by
  unfold tailWord_424920
  simp only [CollatzResearch.WordTrace]
  refine ⟨7749052810297442701736107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10332070413729923602314809 7749052810297442701736107)
  ·
    refine ⟨11623579215446164052604161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7749052810297442701736107 11623579215446164052604161)
    ·
      refine ⟨8717684411584623039453121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11623579215446164052604161 8717684411584623039453121)
      ·
        refine ⟨6538263308688467279589841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8717684411584623039453121 6538263308688467279589841)
        ·
          refine ⟨4903697481516350459692381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6538263308688467279589841 4903697481516350459692381)
          ·
            refine ⟨1838886555568631422384643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4903697481516350459692381 1838886555568631422384643)
            ·
              refine ⟨2758329833352947133576965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1838886555568631422384643 2758329833352947133576965)
              ·
                refine ⟨517186843753677587545681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2758329833352947133576965 517186843753677587545681)
                ·
                  refine ⟨387890132815258190659261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 517186843753677587545681 387890132815258190659261)
                  ·
                    refine ⟨145458799805721821497223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 387890132815258190659261 145458799805721821497223)
                    ·
                      rfl

theorem cell22_424920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 2, 3].length) (baseStart_424920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_424920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_424920 prefixEnd_424920 := by exact prefixLift 424920
  have htrace : WordTrace (prefixWord ++ tailWord_424920) baseStart_424920 baseEnd_424920 := by
    simpa [prefixWord, tailWord_424920, baseEnd_424920] using wordTrace_append hprefix tailTrace_424920
  have hstable : (prefixWord ++ tailWord_424920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424920).length < 2 ^ (prefixWord ++ tailWord_424920).sum := by decide
  have hdescent : baseEnd_424920 < baseStart_424920 := by decide
  rcases family_descends (prefixWord ++ tailWord_424920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_424922 : List Nat := [3, 1, 1, 2, 4, 1, 4, 2, 4]
def baseStart_424922 : Nat := 118140960795 + 424922 * 2 ^ 59
def prefixEnd_424922 : Nat := 4983230072969 + 3 ^ 40 * 424922 * 2
def baseEnd_424922 : Nat := 48486494815531494315739

theorem tailTrace_424922 : CollatzResearch.WordTrace tailWord_424922 prefixEnd_424922 48486494815531494315739 := by
  unfold tailWord_424922
  simp only [CollatzResearch.WordTrace]
  refine ⟨3874544641646909936261255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10332119044391759830030013 3874544641646909936261255)
  ·
    refine ⟨5811816962470364904391883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3874544641646909936261255 5811816962470364904391883)
    ·
      refine ⟨8717725443705547356587825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5811816962470364904391883 8717725443705547356587825)
      ·
        refine ⟨6538294082779160517440869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8717725443705547356587825 6538294082779160517440869)
        ·
          refine ⟨1225930140521092597020163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6538294082779160517440869 1225930140521092597020163)
          ·
            refine ⟨1838895210781638895530245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1225930140521092597020163 1838895210781638895530245)
            ·
              refine ⟨344792852021557292911921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1838895210781638895530245 344792852021557292911921)
              ·
                refine ⟨258594639016167969683941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 344792852021557292911921 258594639016167969683941)
                ·
                  refine ⟨48486494815531494315739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 258594639016167969683941 48486494815531494315739)
                  ·
                    rfl

theorem cell22_424922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 2, 4].length) (baseStart_424922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_424922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_424922 prefixEnd_424922 := by exact prefixLift 424922
  have htrace : WordTrace (prefixWord ++ tailWord_424922) baseStart_424922 baseEnd_424922 := by
    simpa [prefixWord, tailWord_424922, baseEnd_424922] using wordTrace_append hprefix tailTrace_424922
  have hstable : (prefixWord ++ tailWord_424922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_424922).length < 2 ^ (prefixWord ++ tailWord_424922).sum := by decide
  have hdescent : baseEnd_424922 < baseStart_424922 := by decide
  rcases family_descends (prefixWord ++ tailWord_424922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425040 : List Nat := [2, 1, 1, 1, 1, 3, 1, 8, 4]
def baseStart_425040 : Nat := 118140960795 + 425040 * 2 ^ 59
def prefixEnd_425040 : Nat := 4983230072969 + 3 ^ 40 * 425040 * 2
def baseEnd_425040 : Nat := 48499959419360502832285

theorem tailTrace_425040 : CollatzResearch.WordTrace tailWord_425040 prefixEnd_425040 48499959419360502832285 := by
  unfold tailWord_425040
  simp only [CollatzResearch.WordTrace]
  refine ⟨7751241190080072948920287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10334988253440097265227049 7751241190080072948920287)
  ·
    refine ⟨11626861785120109423380431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7751241190080072948920287 11626861785120109423380431)
    ·
      refine ⟨17440292677680164135070647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11626861785120109423380431 17440292677680164135070647)
      ·
        refine ⟨26160439016520246202605971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17440292677680164135070647 26160439016520246202605971)
        ·
          refine ⟨39240658524780369303908957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26160439016520246202605971 39240658524780369303908957)
          ·
            refine ⟨14715246946792638488965859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39240658524780369303908957 14715246946792638488965859)
            ·
              refine ⟨22072870420188957733448789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14715246946792638488965859 22072870420188957733448789)
              ·
                refine ⟨258666450236589348438853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 22072870420188957733448789 258666450236589348438853)
                ·
                  refine ⟨48499959419360502832285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 258666450236589348438853 48499959419360502832285)
                  ·
                    rfl

theorem cell22_425040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 8, 4].length) (baseStart_425040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_425040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_425040 prefixEnd_425040 := by exact prefixLift 425040
  have htrace : WordTrace (prefixWord ++ tailWord_425040) baseStart_425040 baseEnd_425040 := by
    simpa [prefixWord, tailWord_425040, baseEnd_425040] using wordTrace_append hprefix tailTrace_425040
  have hstable : (prefixWord ++ tailWord_425040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425040).length < 2 ^ (prefixWord ++ tailWord_425040).sum := by decide
  have hdescent : baseEnd_425040 < baseStart_425040 := by decide
  rcases family_descends (prefixWord ++ tailWord_425040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425068 : List Nat := [2, 2, 1, 1, 3, 2, 1, 10]
def baseStart_425068 : Nat := 118140960795 + 425068 * 2 ^ 59
def prefixEnd_425068 : Nat := 4983230072969 + 3 ^ 40 * 425068 * 2
def baseEnd_425068 : Nat := 16167718136699863199641

theorem tailTrace_425068 : CollatzResearch.WordTrace tailWord_425068 prefixEnd_425068 16167718136699863199641 := by
  unfold tailWord_425068
  simp only [CollatzResearch.WordTrace]
  refine ⟨7751751812029353339929929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10335669082705804453239905 7751751812029353339929929)
  ·
    refine ⟨5813813859022015004947447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7751751812029353339929929 5813813859022015004947447)
    ·
      refine ⟨8720720788533022507421171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5813813859022015004947447 8720720788533022507421171)
      ·
        refine ⟨13081081182799533761131757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8720720788533022507421171 13081081182799533761131757)
        ·
          refine ⟨4905405443549825160424409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13081081182799533761131757 4905405443549825160424409)
          ·
            refine ⟨3679054082662368870318307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4905405443549825160424409 3679054082662368870318307)
            ·
              refine ⟨5518581123993553305477461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3679054082662368870318307 5518581123993553305477461)
              ·
                refine ⟨16167718136699863199641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5518581123993553305477461 16167718136699863199641)
                ·
                  rfl

theorem cell22_425068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 10].length) (baseStart_425068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_425068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_425068 prefixEnd_425068 := by exact prefixLift 425068
  have htrace : WordTrace (prefixWord ++ tailWord_425068) baseStart_425068 baseEnd_425068 := by
    simpa [prefixWord, tailWord_425068, baseEnd_425068] using wordTrace_append hprefix tailTrace_425068
  have hstable : (prefixWord ++ tailWord_425068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425068).length < 2 ^ (prefixWord ++ tailWord_425068).sum := by decide
  have hdescent : baseEnd_425068 < baseStart_425068 := by decide
  rcases family_descends (prefixWord ++ tailWord_425068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425089 : List Nat := [1, 2, 4, 2, 2, 2, 2, 2, 2, 3]
def baseStart_425089 : Nat := 118140960795 + 425089 * 2 ^ 59
def prefixEnd_425089 : Nat := 4983230072969 + 3 ^ 40 * 425089 * 2
def baseEnd_425089 : Nat := 145516651959461714021705

theorem tailTrace_425089 : CollatzResearch.WordTrace tailWord_425089 prefixEnd_425089 145516651959461714021705 := by
  unfold tailWord_425089
  simp only [CollatzResearch.WordTrace]
  refine ⟨15504269556982627266374321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10336179704655084844249547 15504269556982627266374321)
  ·
    refine ⟨11628202167736970449780741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15504269556982627266374321 11628202167736970449780741)
    ·
      refine ⟨2180287906450681959333889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11628202167736970449780741 2180287906450681959333889)
      ·
        refine ⟨1635215929838011469500417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2180287906450681959333889 1635215929838011469500417)
        ·
          refine ⟨1226411947378508602125313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1635215929838011469500417 1226411947378508602125313)
          ·
            refine ⟨919808960533881451593985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1226411947378508602125313 919808960533881451593985)
            ·
              refine ⟨689856720400411088695489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 919808960533881451593985 689856720400411088695489)
              ·
                refine ⟨517392540300308316521617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 689856720400411088695489 517392540300308316521617)
                ·
                  refine ⟨388044405225231237391213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 517392540300308316521617 388044405225231237391213)
                  ·
                    refine ⟨145516651959461714021705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 388044405225231237391213 145516651959461714021705)
                    ·
                      rfl

theorem cell22_425089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_425089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_425089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_425089 prefixEnd_425089 := by exact prefixLift 425089
  have htrace : WordTrace (prefixWord ++ tailWord_425089) baseStart_425089 baseEnd_425089 := by
    simpa [prefixWord, tailWord_425089, baseEnd_425089] using wordTrace_append hprefix tailTrace_425089
  have hstable : (prefixWord ++ tailWord_425089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425089).length < 2 ^ (prefixWord ++ tailWord_425089).sum := by decide
  have hdescent : baseEnd_425089 < baseStart_425089 := by decide
  rcases family_descends (prefixWord ++ tailWord_425089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425100 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 7, 3]
def baseStart_425100 : Nat := 118140960795 + 425100 * 2 ^ 59
def prefixEnd_425100 : Nat := 4983230072969 + 3 ^ 40 * 425100 * 2
def baseEnd_425100 : Nat := 145520417484261351996671

theorem tailTrace_425100 : CollatzResearch.WordTrace tailWord_425100 prefixEnd_425100 145520417484261351996671 := by
  unfold tailWord_425100
  simp only [CollatzResearch.WordTrace]
  refine ⟨7752335379971388072512377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10336447173295184096683169 7752335379971388072512377)
  ·
    refine ⟨5814251534978541054384283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7752335379971388072512377 5814251534978541054384283)
    ·
      refine ⟨8721377302467811581576425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5814251534978541054384283 8721377302467811581576425)
      ·
        refine ⟨6541032976850858686182319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8721377302467811581576425 6541032976850858686182319)
        ·
          refine ⟨9811549465276288029273479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6541032976850858686182319 9811549465276288029273479)
          ·
            refine ⟨14717324197914432043910219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9811549465276288029273479 14717324197914432043910219)
            ·
              refine ⟨22075986296871648065865329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14717324197914432043910219 22075986296871648065865329)
              ·
                refine ⟨16556989722653736049398997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22075986296871648065865329 16556989722653736049398997)
                ·
                  refine ⟨388054446624696938657789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16556989722653736049398997 388054446624696938657789)
                  ·
                    refine ⟨145520417484261351996671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 388054446624696938657789 145520417484261351996671)
                    ·
                      rfl

theorem cell22_425100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 7, 3].length) (baseStart_425100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_425100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_425100 prefixEnd_425100 := by exact prefixLift 425100
  have htrace : WordTrace (prefixWord ++ tailWord_425100) baseStart_425100 baseEnd_425100 := by
    simpa [prefixWord, tailWord_425100, baseEnd_425100] using wordTrace_append hprefix tailTrace_425100
  have hstable : (prefixWord ++ tailWord_425100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425100).length < 2 ^ (prefixWord ++ tailWord_425100).sum := by decide
  have hdescent : baseEnd_425100 < baseStart_425100 := by decide
  rcases family_descends (prefixWord ++ tailWord_425100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425102 : List Nat := [4, 1, 1, 3, 2, 3, 1, 7]
def baseStart_425102 : Nat := 118140960795 + 425102 * 2 ^ 59
def prefixEnd_425102 : Nat := 4983230072969 + 3 ^ 40 * 425102 * 2
def baseEnd_425102 : Nat := 16169011347237112605185

theorem tailTrace_425102 : CollatzResearch.WordTrace tailWord_425102 prefixEnd_425102 16169011347237112605185 := by
  unfold tailWord_425102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1938092963241941310824695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10336495803957020324398373 1938092963241941310824695)
  ·
    refine ⟨2907139444862911966237043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1938092963241941310824695 2907139444862911966237043)
    ·
      refine ⟨4360709167294367949355565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2907139444862911966237043 4360709167294367949355565)
      ·
        refine ⟨1635265937735387981008337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4360709167294367949355565 1635265937735387981008337)
        ·
          refine ⟨1226449453301540985756253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1635265937735387981008337 1226449453301540985756253)
          ·
            refine ⟨459918544988077869658595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1226449453301540985756253 459918544988077869658595)
            ·
              refine ⟨689877817482116804487893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 459918544988077869658595 689877817482116804487893)
              ·
                refine ⟨16169011347237112605185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 689877817482116804487893 16169011347237112605185)
                ·
                  rfl

theorem cell22_425102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 7].length) (baseStart_425102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_425102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_425102 prefixEnd_425102 := by exact prefixLift 425102
  have htrace : WordTrace (prefixWord ++ tailWord_425102) baseStart_425102 baseEnd_425102 := by
    simpa [prefixWord, tailWord_425102, baseEnd_425102] using wordTrace_append hprefix tailTrace_425102
  have hstable : (prefixWord ++ tailWord_425102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425102).length < 2 ^ (prefixWord ++ tailWord_425102).sum := by decide
  have hdescent : baseEnd_425102 < baseStart_425102 := by decide
  rcases family_descends (prefixWord ++ tailWord_425102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425113 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 11]
def baseStart_425113 : Nat := 118140960795 + 425113 * 2 ^ 59
def prefixEnd_425113 : Nat := 4983230072969 + 3 ^ 40 * 425113 * 2
def baseEnd_425113 : Nat := 48508289216644550473877

theorem tailTrace_425113 : CollatzResearch.WordTrace tailWord_425113 prefixEnd_425113 48508289216644550473877 := by
  unfold tailWord_425113
  simp only [CollatzResearch.WordTrace]
  refine ⟨15505144908895679365247993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10336763272597119576831995 15505144908895679365247993)
  ·
    refine ⟨11628858681671759523935995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15505144908895679365247993 11628858681671759523935995)
    ·
      refine ⟨17443288022507639285903993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11628858681671759523935995 17443288022507639285903993)
      ·
        refine ⟨13082466016880729464427995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17443288022507639285903993 13082466016880729464427995)
        ·
          refine ⟨19623699025321094196641993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13082466016880729464427995 19623699025321094196641993)
          ·
            refine ⟨14717774268990820647481495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19623699025321094196641993 14717774268990820647481495)
            ·
              refine ⟨22076661403486230971222243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14717774268990820647481495 22076661403486230971222243)
              ·
                refine ⟨33114992105229346456833365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22076661403486230971222243 33114992105229346456833365)
                ·
                  refine ⟨48508289216644550473877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 33114992105229346456833365 48508289216644550473877)
                  ·
                    rfl

theorem cell22_425113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 11].length) (baseStart_425113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_425113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_425113 prefixEnd_425113 := by exact prefixLift 425113
  have htrace : WordTrace (prefixWord ++ tailWord_425113) baseStart_425113 baseEnd_425113 := by
    simpa [prefixWord, tailWord_425113, baseEnd_425113] using wordTrace_append hprefix tailTrace_425113
  have hstable : (prefixWord ++ tailWord_425113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425113).length < 2 ^ (prefixWord ++ tailWord_425113).sum := by decide
  have hdescent : baseEnd_425113 < baseStart_425113 := by decide
  rcases family_descends (prefixWord ++ tailWord_425113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425117 : List Nat := [1, 4, 2, 1, 1, 2, 3, 2, 3, 3]
def baseStart_425117 : Nat := 118140960795 + 425117 * 2 ^ 59
def prefixEnd_425117 : Nat := 4983230072969 + 3 ^ 40 * 425117 * 2
def baseEnd_425117 : Nat := 145526236931678974321619

theorem tailTrace_425117 : CollatzResearch.WordTrace tailWord_425117 prefixEnd_425117 145526236931678974321619 := by
  unfold tailWord_425117
  simp only [CollatzResearch.WordTrace]
  refine ⟨15505290800881188048393605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10336860533920792032262403 15505290800881188048393605)
  ·
    refine ⟨2907242025165222759073801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15505290800881188048393605 2907242025165222759073801)
    ·
      refine ⟨2180431518873917069305351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2907242025165222759073801 2180431518873917069305351)
      ·
        refine ⟨3270647278310875603958027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2180431518873917069305351 3270647278310875603958027)
        ·
          refine ⟨4905970917466313405937041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3270647278310875603958027 4905970917466313405937041)
          ·
            refine ⟨3679478188099735054452781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4905970917466313405937041 3679478188099735054452781)
            ·
              refine ⟨1379804320537400645419793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3679478188099735054452781 1379804320537400645419793)
              ·
                refine ⟨1034853240403050484064845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1379804320537400645419793 1034853240403050484064845)
                ·
                  refine ⟨388069965151143931524317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1034853240403050484064845 388069965151143931524317)
                  ·
                    refine ⟨145526236931678974321619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 388069965151143931524317 145526236931678974321619)
                    ·
                      rfl

theorem cell22_425117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_425117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_425117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_425117 prefixEnd_425117 := by exact prefixLift 425117
  have htrace : WordTrace (prefixWord ++ tailWord_425117) baseStart_425117 baseEnd_425117 := by
    simpa [prefixWord, tailWord_425117, baseEnd_425117] using wordTrace_append hprefix tailTrace_425117
  have hstable : (prefixWord ++ tailWord_425117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425117).length < 2 ^ (prefixWord ++ tailWord_425117).sum := by decide
  have hdescent : baseEnd_425117 < baseStart_425117 := by decide
  rcases family_descends (prefixWord ++ tailWord_425117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425145 : List Nat := [1, 2, 1, 4, 1, 3, 1, 2, 2, 5]
def baseStart_425145 : Nat := 118140960795 + 425145 * 2 ^ 59
def prefixEnd_425145 : Nat := 4983230072969 + 3 ^ 40 * 425145 * 2
def baseEnd_425145 : Nat := 145535821903896234621533

theorem tailTrace_425145 : CollatzResearch.WordTrace tailWord_425145 prefixEnd_425145 145535821903896234621533 := by
  unfold tailWord_425145
  simp only [CollatzResearch.WordTrace]
  refine ⟨15506312044779748830412889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10337541363186499220275259 15506312044779748830412889)
  ·
    refine ⟨11629734033584811622809667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15506312044779748830412889 11629734033584811622809667)
    ·
      refine ⟨17444601050377217434214501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11629734033584811622809667 17444601050377217434214501)
      ·
        refine ⟨3270862696945728268915219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17444601050377217434214501 3270862696945728268915219)
        ·
          refine ⟨4906294045418592403372829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3270862696945728268915219 4906294045418592403372829)
          ·
            refine ⟨1839860267031972151264811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4906294045418592403372829 1839860267031972151264811)
            ·
              refine ⟨2759790400547958226897217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1839860267031972151264811 2759790400547958226897217)
              ·
                refine ⟨2069842800410968670172913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2759790400547958226897217 2069842800410968670172913)
                ·
                  refine ⟨1552382100308226502629685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2069842800410968670172913 1552382100308226502629685)
                  ·
                    refine ⟨145535821903896234621533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1552382100308226502629685 145535821903896234621533)
                    ·
                      rfl

theorem cell22_425145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 5].length) (baseStart_425145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_425145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_425145 prefixEnd_425145 := by exact prefixLift 425145
  have htrace : WordTrace (prefixWord ++ tailWord_425145) baseStart_425145 baseEnd_425145 := by
    simpa [prefixWord, tailWord_425145, baseEnd_425145] using wordTrace_append hprefix tailTrace_425145
  have hstable : (prefixWord ++ tailWord_425145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425145).length < 2 ^ (prefixWord ++ tailWord_425145).sum := by decide
  have hdescent : baseEnd_425145 < baseStart_425145 := by decide
  rcases family_descends (prefixWord ++ tailWord_425145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425160 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 5, 4]
def baseStart_425160 : Nat := 118140960795 + 425160 * 2 ^ 59
def prefixEnd_425160 : Nat := 4983230072969 + 3 ^ 40 * 425160 * 2
def baseEnd_425160 : Nat := 145540956710441195496487

theorem tailTrace_425160 : CollatzResearch.WordTrace tailWord_425160 prefixEnd_425160 145540956710441195496487 := by
  unfold tailWord_425160
  simp only [CollatzResearch.WordTrace]
  refine ⟨7753429569862703196104467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10337906093150270928139289 7753429569862703196104467)
  ·
    refine ⟨11630144354794054794156701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7753429569862703196104467 11630144354794054794156701)
    ·
      refine ⟨4361304133047770547808763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11630144354794054794156701 4361304133047770547808763)
      ·
        refine ⟨6541956199571655821713145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4361304133047770547808763 6541956199571655821713145)
        ·
          refine ⟨4906467149678741866284859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6541956199571655821713145 4906467149678741866284859)
          ·
            refine ⟨7359700724518112799427289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4906467149678741866284859 7359700724518112799427289)
            ·
              refine ⟨5519775543388584599570467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7359700724518112799427289 5519775543388584599570467)
              ·
                refine ⟨8279663315082876899355701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5519775543388584599570467 8279663315082876899355701)
                ·
                  refine ⟨776218435789019709314597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8279663315082876899355701 776218435789019709314597)
                  ·
                    refine ⟨145540956710441195496487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 776218435789019709314597 145540956710441195496487)
                    ·
                      rfl

theorem cell22_425160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_425160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_425160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_425160 prefixEnd_425160 := by exact prefixLift 425160
  have htrace : WordTrace (prefixWord ++ tailWord_425160) baseStart_425160 baseEnd_425160 := by
    simpa [prefixWord, tailWord_425160, baseEnd_425160] using wordTrace_append hprefix tailTrace_425160
  have hstable : (prefixWord ++ tailWord_425160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425160).length < 2 ^ (prefixWord ++ tailWord_425160).sum := by decide
  have hdescent : baseEnd_425160 < baseStart_425160 := by decide
  rcases family_descends (prefixWord ++ tailWord_425160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425175 : List Nat := [1, 1, 3, 2, 1, 2, 4, 2, 6]
def baseStart_425175 : Nat := 118140960795 + 425175 * 2 ^ 59
def prefixEnd_425175 : Nat := 4983230072969 + 3 ^ 40 * 425175 * 2
def baseEnd_425175 : Nat := 48515363838995385457147

theorem tailTrace_425175 : CollatzResearch.WordTrace tailWord_425175 prefixEnd_425175 48515363838995385457147 := by
  unfold tailWord_425175
  simp only [CollatzResearch.WordTrace]
  refine ⟨15507406234671063954004979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10338270823114042636003319 15507406234671063954004979)
  ·
    refine ⟨23261109352006595931007469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15507406234671063954004979 23261109352006595931007469)
    ·
      refine ⟨8722916007002473474127801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23261109352006595931007469 8722916007002473474127801)
      ·
        refine ⟨6542187005251855105595851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8722916007002473474127801 6542187005251855105595851)
        ·
          refine ⟨9813280507877782658393777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6542187005251855105595851 9813280507877782658393777)
          ·
            refine ⟨7359960380908336993795333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9813280507877782658393777 7359960380908336993795333)
            ·
              refine ⟨1379992571420313186336625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7359960380908336993795333 1379992571420313186336625)
              ·
                refine ⟨1034994428565234889752469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1379992571420313186336625 1034994428565234889752469)
                ·
                  refine ⟨48515363838995385457147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1034994428565234889752469 48515363838995385457147)
                  ·
                    rfl

theorem cell22_425175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 6].length) (baseStart_425175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_425175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_425175 prefixEnd_425175 := by exact prefixLift 425175
  have htrace : WordTrace (prefixWord ++ tailWord_425175) baseStart_425175 baseEnd_425175 := by
    simpa [prefixWord, tailWord_425175, baseEnd_425175] using wordTrace_append hprefix tailTrace_425175
  have hstable : (prefixWord ++ tailWord_425175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425175).length < 2 ^ (prefixWord ++ tailWord_425175).sum := by decide
  have hdescent : baseEnd_425175 < baseStart_425175 := by decide
  rcases family_descends (prefixWord ++ tailWord_425175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425209 : List Nat := [1, 2, 1, 3, 1, 1, 7, 2, 4]
def baseStart_425209 : Nat := 118140960795 + 425209 * 2 ^ 59
def prefixEnd_425209 : Nat := 4983230072969 + 3 ^ 40 * 425209 * 2
def baseEnd_425209 : Nat := 48519243470607133673779

theorem tailTrace_425209 : CollatzResearch.WordTrace tailWord_425209 prefixEnd_425209 48519243470607133673779 := by
  unfold tailWord_425209
  simp only [CollatzResearch.WordTrace]
  refine ⟨15508646316547887760742681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10339097544365258507161787 15508646316547887760742681)
  ·
    refine ⟨11631484737410915820557011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15508646316547887760742681 11631484737410915820557011)
    ·
      refine ⟨17447227106116373730835517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11631484737410915820557011 17447227106116373730835517)
      ·
        refine ⟨6542710164793640149063319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17447227106116373730835517 6542710164793640149063319)
        ·
          refine ⟨9814065247190460223594979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6542710164793640149063319 9814065247190460223594979)
          ·
            refine ⟨14721097870785690335392469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9814065247190460223594979 14721097870785690335392469)
            ·
              refine ⟨345025731346539617235761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 14721097870785690335392469 345025731346539617235761)
              ·
                refine ⟨258769298509904712926821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 345025731346539617235761 258769298509904712926821)
                ·
                  refine ⟨48519243470607133673779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 258769298509904712926821 48519243470607133673779)
                  ·
                    rfl

theorem cell22_425209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 2, 4].length) (baseStart_425209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_425209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_425209 prefixEnd_425209 := by exact prefixLift 425209
  have htrace : WordTrace (prefixWord ++ tailWord_425209) baseStart_425209 baseEnd_425209 := by
    simpa [prefixWord, tailWord_425209, baseEnd_425209] using wordTrace_append hprefix tailTrace_425209
  have hstable : (prefixWord ++ tailWord_425209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425209).length < 2 ^ (prefixWord ++ tailWord_425209).sum := by decide
  have hdescent : baseEnd_425209 < baseStart_425209 := by decide
  rcases family_descends (prefixWord ++ tailWord_425209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425327 : List Nat := [1, 1, 2, 1, 3, 1, 6, 1, 6]
def baseStart_425327 : Nat := 118140960795 + 425327 * 2 ^ 59
def prefixEnd_425327 : Nat := 4983230072969 + 3 ^ 40 * 425327 * 2
def baseEnd_425327 : Nat := 48532708074436142190325

theorem tailTrace_425327 : CollatzResearch.WordTrace tailWord_425327 prefixEnd_425327 48532708074436142190325 := by
  unfold tailWord_425327
  simp only [CollatzResearch.WordTrace]
  refine ⟨15512950130120393913538235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10341966753413595942358823 15512950130120393913538235)
  ·
    refine ⟨23269425195180590870307353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15512950130120393913538235 23269425195180590870307353)
    ·
      refine ⟨17452068896385443152730515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23269425195180590870307353 17452068896385443152730515)
      ·
        refine ⟨26178103344578164729095773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17452068896385443152730515 26178103344578164729095773)
        ·
          refine ⟨9816788754216811773410915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26178103344578164729095773 9816788754216811773410915)
          ·
            refine ⟨14725183131325217660116373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9816788754216811773410915 14725183131325217660116373)
            ·
              refine ⟨690242959280869577817955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14725183131325217660116373 690242959280869577817955)
              ·
                refine ⟨1035364438921304366726933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 690242959280869577817955 1035364438921304366726933)
                ·
                  refine ⟨48532708074436142190325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1035364438921304366726933 48532708074436142190325)
                  ·
                    rfl

theorem cell22_425327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 6].length) (baseStart_425327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_425327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_425327 prefixEnd_425327 := by exact prefixLift 425327
  have htrace : WordTrace (prefixWord ++ tailWord_425327) baseStart_425327 baseEnd_425327 := by
    simpa [prefixWord, tailWord_425327, baseEnd_425327] using wordTrace_append hprefix tailTrace_425327
  have hstable : (prefixWord ++ tailWord_425327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425327).length < 2 ^ (prefixWord ++ tailWord_425327).sum := by decide
  have hdescent : baseEnd_425327 < baseStart_425327 := by decide
  rcases family_descends (prefixWord ++ tailWord_425327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425378 : List Nat := [3, 3, 1, 2, 1, 3, 3, 2, 4]
def baseStart_425378 : Nat := 118140960795 + 425378 * 2 ^ 59
def prefixEnd_425378 : Nat := 4983230072969 + 3 ^ 40 * 425378 * 2
def baseEnd_425378 : Nat := 48538527521853764515273

theorem tailTrace_425378 : CollatzResearch.WordTrace tailWord_425378 prefixEnd_425378 48538527521853764515273 := by
  unfold tailWord_425378
  simp only [CollatzResearch.WordTrace]
  refine ⟨3878702563233907405911197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10343206835290419749096525 3878702563233907405911197)
  ·
    refine ⟨1454513461212715277216699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3878702563233907405911197 1454513461212715277216699)
    ·
      refine ⟨2181770191819072915825049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1454513461212715277216699 2181770191819072915825049)
      ·
        refine ⟨1636327643864304686868787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2181770191819072915825049 1636327643864304686868787)
        ·
          refine ⟨2454491465796457030303181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1636327643864304686868787 2454491465796457030303181)
          ·
            refine ⟨920434299673671386363693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2454491465796457030303181 920434299673671386363693)
            ·
              refine ⟨345162862377626769886385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 920434299673671386363693 345162862377626769886385)
              ·
                refine ⟨258872146783220077414789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 345162862377626769886385 258872146783220077414789)
                ·
                  refine ⟨48538527521853764515273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 258872146783220077414789 48538527521853764515273)
                  ·
                    rfl

theorem cell22_425378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_425378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_425378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_425378 prefixEnd_425378 := by exact prefixLift 425378
  have htrace : WordTrace (prefixWord ++ tailWord_425378) baseStart_425378 baseEnd_425378 := by
    simpa [prefixWord, tailWord_425378, baseEnd_425378] using wordTrace_append hprefix tailTrace_425378
  have hstable : (prefixWord ++ tailWord_425378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425378).length < 2 ^ (prefixWord ++ tailWord_425378).sum := by decide
  have hdescent : baseEnd_425378 < baseStart_425378 := by decide
  rcases family_descends (prefixWord ++ tailWord_425378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425389 : List Nat := [1, 5, 2, 2, 1, 1, 1, 9]
def baseStart_425389 : Nat := 118140960795 + 425389 * 2 ^ 59
def prefixEnd_425389 : Nat := 4983230072969 + 3 ^ 40 * 425389 * 2
def baseEnd_425389 : Nat := 16179927565595659057865

theorem tailTrace_425389 : CollatzResearch.WordTrace tailWord_425389 prefixEnd_425389 16179927565595659057865 := by
  unfold tailWord_425389
  simp only [CollatzResearch.WordTrace]
  refine ⟨15515211455895778502295221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10343474303930519001530147 15515211455895778502295221)
  ·
    refine ⟨1454551073990229234590177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15515211455895778502295221 1454551073990229234590177)
    ·
      refine ⟨1090913305492671925942633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1454551073990229234590177 1090913305492671925942633)
      ·
        refine ⟨818184979119503944456975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1090913305492671925942633 818184979119503944456975)
        ·
          refine ⟨1227277468679255916685463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 818184979119503944456975 1227277468679255916685463)
          ·
            refine ⟨1840916203018883875028195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1227277468679255916685463 1840916203018883875028195)
            ·
              refine ⟨2761374304528325812542293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1840916203018883875028195 2761374304528325812542293)
              ·
                refine ⟨16179927565595659057865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2761374304528325812542293 16179927565595659057865)
                ·
                  rfl

theorem cell22_425389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 9].length) (baseStart_425389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_425389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_425389 prefixEnd_425389 := by exact prefixLift 425389
  have htrace : WordTrace (prefixWord ++ tailWord_425389) baseStart_425389 baseEnd_425389 := by
    simpa [prefixWord, tailWord_425389, baseEnd_425389] using wordTrace_append hprefix tailTrace_425389
  have hstable : (prefixWord ++ tailWord_425389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425389).length < 2 ^ (prefixWord ++ tailWord_425389).sum := by decide
  have hdescent : baseEnd_425389 < baseStart_425389 := by decide
  rcases family_descends (prefixWord ++ tailWord_425389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425434 : List Nat := [3, 1, 1, 2, 3, 2, 1, 4, 5]
def baseStart_425434 : Nat := 118140960795 + 425434 * 2 ^ 59
def prefixEnd_425434 : Nat := 4983230072969 + 3 ^ 40 * 425434 * 2
def baseEnd_425434 : Nat := 48544917503331938048549

theorem tailTrace_425434 : CollatzResearch.WordTrace tailWord_425434 prefixEnd_425434 48544917503331938048549 := by
  unfold tailWord_425434
  simp only [CollatzResearch.WordTrace]
  refine ⟨3879213185183187796920839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10344568493821834125122237 3879213185183187796920839)
  ·
    refine ⟨5818819777774781695381259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3879213185183187796920839 5818819777774781695381259)
    ·
      refine ⟨8728229666662172543071889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5818819777774781695381259 8728229666662172543071889)
      ·
        refine ⟨6546172249996629407303917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8728229666662172543071889 6546172249996629407303917)
        ·
          refine ⟨2454814593748736027738969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6546172249996629407303917 2454814593748736027738969)
          ·
            refine ⟨1841110945311552020804227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2454814593748736027738969 1841110945311552020804227)
            ·
              refine ⟨2761666417967328031206341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1841110945311552020804227 2761666417967328031206341)
              ·
                refine ⟨517812453368874005851189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2761666417967328031206341 517812453368874005851189)
                ·
                  refine ⟨48544917503331938048549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 517812453368874005851189 48544917503331938048549)
                  ·
                    rfl

theorem cell22_425434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 5].length) (baseStart_425434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_425434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_425434 prefixEnd_425434 := by exact prefixLift 425434
  have htrace : WordTrace (prefixWord ++ tailWord_425434) baseStart_425434 baseEnd_425434 := by
    simpa [prefixWord, tailWord_425434, baseEnd_425434] using wordTrace_append hprefix tailTrace_425434
  have hstable : (prefixWord ++ tailWord_425434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425434).length < 2 ^ (prefixWord ++ tailWord_425434).sum := by decide
  have hdescent : baseEnd_425434 < baseStart_425434 := by decide
  rcases family_descends (prefixWord ++ tailWord_425434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425464 : List Nat := [2, 1, 2, 1, 1, 5, 2, 1, 3, 4]
def baseStart_425464 : Nat := 118140960795 + 425464 * 2 ^ 59
def prefixEnd_425464 : Nat := 4983230072969 + 3 ^ 40 * 425464 * 2
def baseEnd_425464 : Nat := 145645022123085735895555

theorem tailTrace_425464 : CollatzResearch.WordTrace tailWord_425464 prefixEnd_425464 145645022123085735895555 := by
  unfold tailWord_425464
  simp only [CollatzResearch.WordTrace]
  refine ⟨7758973465312033155637723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10345297953749377540850297 7758973465312033155637723)
  ·
    refine ⟨11638460197968049733456585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7758973465312033155637723 11638460197968049733456585)
    ·
      refine ⟨8728845148476037300092439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11638460197968049733456585 8728845148476037300092439)
      ·
        refine ⟨13093267722714055950138659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8728845148476037300092439 13093267722714055950138659)
        ·
          refine ⟨19639901584071083925207989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13093267722714055950138659 19639901584071083925207989)
          ·
            refine ⟨1841240773506664117988249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19639901584071083925207989 1841240773506664117988249)
            ·
              refine ⟨1380930580129998088491187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1841240773506664117988249 1380930580129998088491187)
              ·
                refine ⟨2071395870194997132736781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1380930580129998088491187 2071395870194997132736781)
                ·
                  refine ⟨776773451323123924776293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2071395870194997132736781 776773451323123924776293)
                  ·
                    refine ⟨145645022123085735895555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 776773451323123924776293 145645022123085735895555)
                    ·
                      rfl

theorem cell22_425464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_425464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_425464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_425464 prefixEnd_425464 := by exact prefixLift 425464
  have htrace : WordTrace (prefixWord ++ tailWord_425464) baseStart_425464 baseEnd_425464 := by
    simpa [prefixWord, tailWord_425464, baseEnd_425464] using wordTrace_append hprefix tailTrace_425464
  have hstable : (prefixWord ++ tailWord_425464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425464).length < 2 ^ (prefixWord ++ tailWord_425464).sum := by decide
  have hdescent : baseEnd_425464 < baseStart_425464 := by decide
  rcases family_descends (prefixWord ++ tailWord_425464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425496 : List Nat := [2, 1, 2, 3, 4, 1, 2, 1, 6]
def baseStart_425496 : Nat := 118140960795 + 425496 * 2 ^ 59
def prefixEnd_425496 : Nat := 4983230072969 + 3 ^ 40 * 425496 * 2
def baseEnd_425496 : Nat := 48551992125682773031819

theorem tailTrace_425496 : CollatzResearch.WordTrace tailWord_425496 prefixEnd_425496 48551992125682773031819 := by
  unfold tailWord_425496
  simp only [CollatzResearch.WordTrace]
  refine ⟨7759557033254067888220171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10346076044338757184293561 7759557033254067888220171)
  ·
    refine ⟨11639335549881101832330257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7759557033254067888220171 11639335549881101832330257)
    ·
      refine ⟨8729501662410826374247693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11639335549881101832330257 8729501662410826374247693)
      ·
        refine ⟨3273563123404059890342885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8729501662410826374247693 3273563123404059890342885)
        ·
          refine ⟨613793085638261229439291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3273563123404059890342885 613793085638261229439291)
          ·
            refine ⟨920689628457391844158937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 613793085638261229439291 920689628457391844158937)
            ·
              refine ⟨690517221343043883119203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 920689628457391844158937 690517221343043883119203)
              ·
                refine ⟨1035775832014565824678805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 690517221343043883119203 1035775832014565824678805)
                ·
                  refine ⟨48551992125682773031819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1035775832014565824678805 48551992125682773031819)
                  ·
                    rfl

theorem cell22_425496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 6].length) (baseStart_425496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_425496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_425496 prefixEnd_425496 := by exact prefixLift 425496
  have htrace : WordTrace (prefixWord ++ tailWord_425496) baseStart_425496 baseEnd_425496 := by
    simpa [prefixWord, tailWord_425496, baseEnd_425496] using wordTrace_append hprefix tailTrace_425496
  have hstable : (prefixWord ++ tailWord_425496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425496).length < 2 ^ (prefixWord ++ tailWord_425496).sum := by decide
  have hdescent : baseEnd_425496 < baseStart_425496 := by decide
  rcases family_descends (prefixWord ++ tailWord_425496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425607 : List Nat := [1, 1, 4, 2, 1, 5, 2, 2, 1, 3]
def baseStart_425607 : Nat := 118140960795 + 425607 * 2 ^ 59
def prefixEnd_425607 : Nat := 4983230072969 + 3 ^ 40 * 425607 * 2
def baseEnd_425607 : Nat := 145693973945481029570117

theorem tailTrace_425607 : CollatzResearch.WordTrace tailWord_425607 prefixEnd_425607 145693973945481029570117 := by
  unfold tailWord_425607
  simp only [CollatzResearch.WordTrace]
  refine ⟨15523162569106001733731075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10348775046070667822487383 15523162569106001733731075)
  ·
    refine ⟨23284743853659002600596613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15523162569106001733731075 23284743853659002600596613)
    ·
      refine ⟨4365889472561062987611865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23284743853659002600596613 4365889472561062987611865)
      ·
        refine ⟨3274417104420797240708899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4365889472561062987611865 3274417104420797240708899)
        ·
          refine ⟨4911625656631195861063349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3274417104420797240708899 4911625656631195861063349)
          ·
            refine ⟨460464905309174611974689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4911625656631195861063349 460464905309174611974689)
            ·
              refine ⟨345348678981880958981017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 460464905309174611974689 345348678981880958981017)
              ·
                refine ⟨259011509236410719235763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 345348678981880958981017 259011509236410719235763)
                ·
                  refine ⟨388517263854616078853645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 259011509236410719235763 388517263854616078853645)
                  ·
                    refine ⟨145693973945481029570117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 388517263854616078853645 145693973945481029570117)
                    ·
                      rfl

theorem cell22_425607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 2, 1, 3].length) (baseStart_425607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_425607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_425607 prefixEnd_425607 := by exact prefixLift 425607
  have htrace : WordTrace (prefixWord ++ tailWord_425607) baseStart_425607 baseEnd_425607 := by
    simpa [prefixWord, tailWord_425607, baseEnd_425607] using wordTrace_append hprefix tailTrace_425607
  have hstable : (prefixWord ++ tailWord_425607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425607).length < 2 ^ (prefixWord ++ tailWord_425607).sum := by decide
  have hdescent : baseEnd_425607 < baseStart_425607 := by decide
  rcases family_descends (prefixWord ++ tailWord_425607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425618 : List Nat := [3, 2, 3, 1, 3, 1, 1, 1, 2, 5]
def baseStart_425618 : Nat := 118140960795 + 425618 * 2 ^ 59
def prefixEnd_425618 : Nat := 4983230072969 + 3 ^ 40 * 425618 * 2
def baseEnd_425618 : Nat := 145697739470280667545083

theorem tailTrace_425618 : CollatzResearch.WordTrace tailWord_425618 prefixEnd_425618 145697739470280667545083 := by
  unfold tailWord_425618
  simp only [CollatzResearch.WordTrace]
  refine ⟨3880890943016537653095377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10349042514710767074921005 3880890943016537653095377)
  ·
    refine ⟨2910668207262403239821533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3880890943016537653095377 2910668207262403239821533)
    ·
      refine ⟨1091500577723401214933075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2910668207262403239821533 1091500577723401214933075)
      ·
        refine ⟨1637250866585101822399613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1091500577723401214933075 1637250866585101822399613)
        ·
          refine ⟨613969074969413183399855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1637250866585101822399613 613969074969413183399855)
          ·
            refine ⟨920953612454119775099783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 613969074969413183399855 920953612454119775099783)
            ·
              refine ⟨1381430418681179662649675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 920953612454119775099783 1381430418681179662649675)
              ·
                refine ⟨2072145628021769493974513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1381430418681179662649675 2072145628021769493974513)
                ·
                  refine ⟨1554109221016327120480885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2072145628021769493974513 1554109221016327120480885)
                  ·
                    refine ⟨145697739470280667545083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1554109221016327120480885 145697739470280667545083)
                    ·
                      rfl

theorem cell22_425618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_425618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_425618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_425618 prefixEnd_425618 := by exact prefixLift 425618
  have htrace : WordTrace (prefixWord ++ tailWord_425618) baseStart_425618 baseEnd_425618 := by
    simpa [prefixWord, tailWord_425618, baseEnd_425618] using wordTrace_append hprefix tailTrace_425618
  have hstable : (prefixWord ++ tailWord_425618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425618).length < 2 ^ (prefixWord ++ tailWord_425618).sum := by decide
  have hdescent : baseEnd_425618 < baseStart_425618 := by decide
  rcases family_descends (prefixWord ++ tailWord_425618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425661 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 4, 4]
def baseStart_425661 : Nat := 118140960795 + 425661 * 2 ^ 59
def prefixEnd_425661 : Nat := 4983230072969 + 3 ^ 40 * 425661 * 2
def baseEnd_425661 : Nat := 145712459249042888719951

theorem tailTrace_425661 : CollatzResearch.WordTrace tailWord_425661 prefixEnd_425661 145712459249042888719951 := by
  unfold tailWord_425661
  simp only [CollatzResearch.WordTrace]
  refine ⟨15525132110910368956196837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10350088073940245970797891 15525132110910368956196837)
  ·
    refine ⟨2910962270795694179286907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15525132110910368956196837 2910962270795694179286907)
    ·
      refine ⟨4366443406193541268930361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2910962270795694179286907 4366443406193541268930361)
      ·
        refine ⟨3274832554645155951697771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4366443406193541268930361 3274832554645155951697771)
        ·
          refine ⟨4912248831967733927546657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3274832554645155951697771 4912248831967733927546657)
          ·
            refine ⟨3684186623975800445659993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4912248831967733927546657 3684186623975800445659993)
            ·
              refine ⟨2763139967981850334244995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3684186623975800445659993 2763139967981850334244995)
              ·
                refine ⟨4144709951972775501367493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2763139967981850334244995 4144709951972775501367493)
                ·
                  refine ⟨777133115994895406506405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4144709951972775501367493 777133115994895406506405)
                  ·
                    refine ⟨145712459249042888719951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 777133115994895406506405 145712459249042888719951)
                    ·
                      rfl

theorem cell22_425661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_425661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_425661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_425661 prefixEnd_425661 := by exact prefixLift 425661
  have htrace : WordTrace (prefixWord ++ tailWord_425661) baseStart_425661 baseEnd_425661 := by
    simpa [prefixWord, tailWord_425661, baseEnd_425661] using wordTrace_append hprefix tailTrace_425661
  have hstable : (prefixWord ++ tailWord_425661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425661).length < 2 ^ (prefixWord ++ tailWord_425661).sum := by decide
  have hdescent : baseEnd_425661 < baseStart_425661 := by decide
  rcases family_descends (prefixWord ++ tailWord_425661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425736 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 1, 7]
def baseStart_425736 : Nat := 118140960795 + 425736 * 2 ^ 59
def prefixEnd_425736 : Nat := 4983230072969 + 3 ^ 40 * 425736 * 2
def baseEnd_425736 : Nat := 145738133281767693094721

theorem tailTrace_425736 : CollatzResearch.WordTrace tailWord_425736 prefixEnd_425736 145738133281767693094721 := by
  unfold tailWord_425736
  simp only [CollatzResearch.WordTrace]
  refine ⟨7763933792819328382588531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10351911723759104510118041 7763933792819328382588531)
  ·
    refine ⟨11645900689228992573882797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7763933792819328382588531 11645900689228992573882797)
    ·
      refine ⟨4367212758460872215206049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11645900689228992573882797 4367212758460872215206049)
      ·
        refine ⟨3275409568845654161404537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4367212758460872215206049 3275409568845654161404537)
        ·
          refine ⟨2456557176634240621053403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3275409568845654161404537 2456557176634240621053403)
          ·
            refine ⟨3684835764951360931580105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2456557176634240621053403 3684835764951360931580105)
            ·
              refine ⟨2763626823713520698685079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3684835764951360931580105 2763626823713520698685079)
              ·
                refine ⟨4145440235570281048027619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2763626823713520698685079 4145440235570281048027619)
                ·
                  refine ⟨6218160353355421572041429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4145440235570281048027619 6218160353355421572041429)
                  ·
                    refine ⟨145738133281767693094721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6218160353355421572041429 145738133281767693094721)
                    ·
                      rfl

theorem cell22_425736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_425736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_425736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_425736 prefixEnd_425736 := by exact prefixLift 425736
  have htrace : WordTrace (prefixWord ++ tailWord_425736) baseStart_425736 baseEnd_425736 := by
    simpa [prefixWord, tailWord_425736, baseEnd_425736] using wordTrace_append hprefix tailTrace_425736
  have hstable : (prefixWord ++ tailWord_425736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425736).length < 2 ^ (prefixWord ++ tailWord_425736).sum := by decide
  have hdescent : baseEnd_425736 < baseStart_425736 := by decide
  rcases family_descends (prefixWord ++ tailWord_425736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425738 : List Nat := [3, 1, 2, 2, 1, 4, 1, 3, 5]
def baseStart_425738 : Nat := 118140960795 + 425738 * 2 ^ 59
def prefixEnd_425738 : Nat := 4983230072969 + 3 ^ 40 * 425738 * 2
def baseEnd_425738 : Nat := 48579605974213451514905

theorem tailTrace_425738 : CollatzResearch.WordTrace tailWord_425738 prefixEnd_425738 48579605974213451514905 := by
  unfold tailWord_425738
  simp only [CollatzResearch.WordTrace]
  refine ⟨3881985132907852776687467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10351960354420940737833245 3881985132907852776687467)
  ·
    refine ⟨5822977699361779165031201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3881985132907852776687467 5822977699361779165031201)
    ·
      refine ⟨4367233274521334373773401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5822977699361779165031201 4367233274521334373773401)
      ·
        refine ⟨3275424955891000780330051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4367233274521334373773401 3275424955891000780330051)
        ·
          refine ⟨4913137433836501170495077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3275424955891000780330051 4913137433836501170495077)
          ·
            refine ⟨921213268844343969467827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4913137433836501170495077 921213268844343969467827)
            ·
              refine ⟨1381819903266515954201741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 921213268844343969467827 1381819903266515954201741)
              ·
                refine ⟨518182463724943482825653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1381819903266515954201741 518182463724943482825653)
                ·
                  refine ⟨48579605974213451514905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 518182463724943482825653 48579605974213451514905)
                  ·
                    rfl

theorem cell22_425738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 5].length) (baseStart_425738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_425738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_425738 prefixEnd_425738 := by exact prefixLift 425738
  have htrace : WordTrace (prefixWord ++ tailWord_425738) baseStart_425738 baseEnd_425738 := by
    simpa [prefixWord, tailWord_425738, baseEnd_425738] using wordTrace_append hprefix tailTrace_425738
  have hstable : (prefixWord ++ tailWord_425738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425738).length < 2 ^ (prefixWord ++ tailWord_425738).sum := by decide
  have hdescent : baseEnd_425738 < baseStart_425738 := by decide
  rcases family_descends (prefixWord ++ tailWord_425738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425813 : List Nat := [1, 3, 2, 2, 2, 3, 1, 1, 1, 6]
def baseStart_425813 : Nat := 118140960795 + 425813 * 2 ^ 59
def prefixEnd_425813 : Nat := 4983230072969 + 3 ^ 40 * 425813 * 2
def baseEnd_425813 : Nat := 145764491955365158919485

theorem tailTrace_425813 : CollatzResearch.WordTrace tailWord_425813 prefixEnd_425813 145764491955365158919485 := by
  unfold tailWord_425813
  simp only [CollatzResearch.WordTrace]
  refine ⟨15530676006359698915730093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10353784004239799277153395 15530676006359698915730093)
  ·
    refine ⟨5824003502384887093398785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15530676006359698915730093 5824003502384887093398785)
    ·
      refine ⟨4368002626788665320049089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5824003502384887093398785 4368002626788665320049089)
      ·
        refine ⟨3276001970091498990036817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4368002626788665320049089 3276001970091498990036817)
        ·
          refine ⟨2457001477568624242527613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3276001970091498990036817 2457001477568624242527613)
          ·
            refine ⟨921375554088234090947855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2457001477568624242527613 921375554088234090947855)
            ·
              refine ⟨1382063331132351136421783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 921375554088234090947855 1382063331132351136421783)
              ·
                refine ⟨2073094996698526704632675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1382063331132351136421783 2073094996698526704632675)
                ·
                  refine ⟨3109642495047790056949013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2073094996698526704632675 3109642495047790056949013)
                  ·
                    refine ⟨145764491955365158919485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3109642495047790056949013 145764491955365158919485)
                    ·
                      rfl

theorem cell22_425813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_425813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_425813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_425813 prefixEnd_425813 := by exact prefixLift 425813
  have htrace : WordTrace (prefixWord ++ tailWord_425813) baseStart_425813 baseEnd_425813 := by
    simpa [prefixWord, tailWord_425813, baseEnd_425813] using wordTrace_append hprefix tailTrace_425813
  have hstable : (prefixWord ++ tailWord_425813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425813).length < 2 ^ (prefixWord ++ tailWord_425813).sum := by decide
  have hdescent : baseEnd_425813 < baseStart_425813 := by decide
  rcases family_descends (prefixWord ++ tailWord_425813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425828 : List Nat := [2, 3, 1, 1, 5, 1, 9]
def baseStart_425828 : Nat := 118140960795 + 425828 * 2 ^ 59
def prefixEnd_425828 : Nat := 4983230072969 + 3 ^ 40 * 425828 * 2
def baseEnd_425828 : Nat := 5398875065255930362757

theorem tailTrace_425828 : CollatzResearch.WordTrace tailWord_425828 prefixEnd_425828 5398875065255930362757 := by
  unfold tailWord_425828
  simp only [CollatzResearch.WordTrace]
  refine ⟨7765611550652678238763069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10354148734203570985017425 7765611550652678238763069)
  ·
    refine ⟨2912104331494754339536151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7765611550652678238763069 2912104331494754339536151)
    ·
      refine ⟨4368156497242131509304227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2912104331494754339536151 4368156497242131509304227)
      ·
        refine ⟨6552234745863197263956341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4368156497242131509304227 6552234745863197263956341)
        ·
          refine ⟨614272007424674743495907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6552234745863197263956341 614272007424674743495907)
          ·
            refine ⟨921408011137012115243861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614272007424674743495907 921408011137012115243861)
            ·
              refine ⟨5398875065255930362757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 921408011137012115243861 5398875065255930362757)
              ·
                rfl

theorem cell22_425828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 9].length) (baseStart_425828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_425828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_425828 prefixEnd_425828 := by exact prefixLift 425828
  have htrace : WordTrace (prefixWord ++ tailWord_425828) baseStart_425828 baseEnd_425828 := by
    simpa [prefixWord, tailWord_425828, baseEnd_425828] using wordTrace_append hprefix tailTrace_425828
  have hstable : (prefixWord ++ tailWord_425828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425828).length < 2 ^ (prefixWord ++ tailWord_425828).sum := by decide
  have hdescent : baseEnd_425828 < baseStart_425828 := by decide
  rcases family_descends (prefixWord ++ tailWord_425828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425860 : List Nat := [2, 3, 2, 1, 1, 1, 4, 2, 3, 3]
def baseStart_425860 : Nat := 118140960795 + 425860 * 2 ^ 59
def prefixEnd_425860 : Nat := 4983230072969 + 3 ^ 40 * 425860 * 2
def baseEnd_425860 : Nat := 145780581015872702994341

theorem tailTrace_425860 : CollatzResearch.WordTrace tailWord_425860 prefixEnd_425860 145780581015872702994341 := by
  unfold tailWord_425860
  simp only [CollatzResearch.WordTrace]
  refine ⟨7766195118594712971345517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10354926824792950628460689 7766195118594712971345517)
  ·
    refine ⟨2912323169473017364254569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7766195118594712971345517 2912323169473017364254569)
    ·
      refine ⟨2184242377104763023190927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2912323169473017364254569 2184242377104763023190927)
      ·
        refine ⟨3276363565657144534786391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2184242377104763023190927 3276363565657144534786391)
        ·
          refine ⟨4914545348485716802179587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3276363565657144534786391 4914545348485716802179587)
          ·
            refine ⟨7371818022728575203269381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4914545348485716802179587 7371818022728575203269381)
            ·
              refine ⟨1382215879261607850613009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7371818022728575203269381 1382215879261607850613009)
              ·
                refine ⟨1036661909446205887959757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1382215879261607850613009 1036661909446205887959757)
                ·
                  refine ⟨388748216042327207984909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1036661909446205887959757 388748216042327207984909)
                  ·
                    refine ⟨145780581015872702994341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 388748216042327207984909 145780581015872702994341)
                    ·
                      rfl

theorem cell22_425860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_425860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_425860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_425860 prefixEnd_425860 := by exact prefixLift 425860
  have htrace : WordTrace (prefixWord ++ tailWord_425860) baseStart_425860 baseEnd_425860 := by
    simpa [prefixWord, tailWord_425860, baseEnd_425860] using wordTrace_append hprefix tailTrace_425860
  have hstable : (prefixWord ++ tailWord_425860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425860).length < 2 ^ (prefixWord ++ tailWord_425860).sum := by decide
  have hdescent : baseEnd_425860 < baseStart_425860 := by decide
  rcases family_descends (prefixWord ++ tailWord_425860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425903 : List Nat := [1, 1, 2, 1, 2, 2, 4, 2, 3, 4]
def baseStart_425903 : Nat := 118140960795 + 425903 * 2 ^ 59
def prefixEnd_425903 : Nat := 4983230072969 + 3 ^ 40 * 425903 * 2
def baseEnd_425903 : Nat := 145795300794634924169209

theorem tailTrace_425903 : CollatzResearch.WordTrace tailWord_425903 prefixEnd_425903 145795300794634924169209 := by
  unfold tailWord_425903
  simp only [CollatzResearch.WordTrace]
  refine ⟨15533958576033644286506363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10355972384022429524337575 15533958576033644286506363)
  ·
    refine ⟨23300937864050466429759545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15533958576033644286506363 23300937864050466429759545)
    ·
      refine ⟨17475703398037849822319659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23300937864050466429759545 17475703398037849822319659)
      ·
        refine ⟨26213555097056774733479489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17475703398037849822319659 26213555097056774733479489)
        ·
          refine ⟨19660166322792581050109617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26213555097056774733479489 19660166322792581050109617)
          ·
            refine ⟨14745124742094435787582213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19660166322792581050109617 14745124742094435787582213)
            ·
              refine ⟨2764710889142706710171665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14745124742094435787582213 2764710889142706710171665)
              ·
                refine ⟨2073533166857030032628749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2764710889142706710171665 2073533166857030032628749)
                ·
                  refine ⟨777574937571386262235781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2073533166857030032628749 777574937571386262235781)
                  ·
                    refine ⟨145795300794634924169209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 777574937571386262235781 145795300794634924169209)
                    ·
                      rfl

theorem cell22_425903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 4].length) (baseStart_425903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_425903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_425903 prefixEnd_425903 := by exact prefixLift 425903
  have htrace : WordTrace (prefixWord ++ tailWord_425903) baseStart_425903 baseEnd_425903 := by
    simpa [prefixWord, tailWord_425903, baseEnd_425903] using wordTrace_append hprefix tailTrace_425903
  have hstable : (prefixWord ++ tailWord_425903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425903).length < 2 ^ (prefixWord ++ tailWord_425903).sum := by decide
  have hdescent : baseEnd_425903 < baseStart_425903 := by decide
  rcases family_descends (prefixWord ++ tailWord_425903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425935 : List Nat := [1, 1, 2, 1, 1, 5, 2, 5, 4]
def baseStart_425935 : Nat := 118140960795 + 425935 * 2 ^ 59
def prefixEnd_425935 : Nat := 4983230072969 + 3 ^ 40 * 425935 * 2
def baseEnd_425935 : Nat := 48602085016199169123037

theorem tailTrace_425935 : CollatzResearch.WordTrace tailWord_425935 prefixEnd_425935 48602085016199169123037 := by
  unfold tailWord_425935
  simp only [CollatzResearch.WordTrace]
  refine ⟨15535125711917713751671259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10356750474611809167780839 15535125711917713751671259)
  ·
    refine ⟨23302688567876570627506889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15535125711917713751671259 23302688567876570627506889)
    ·
      refine ⟨17477016425907427970630167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23302688567876570627506889 17477016425907427970630167)
      ·
        refine ⟨26215524638861141955945251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17477016425907427970630167 26215524638861141955945251)
        ·
          refine ⟨39323286958291712933917877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26215524638861141955945251 39323286958291712933917877)
          ·
            refine ⟨3686558152339848087554801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39323286958291712933917877 3686558152339848087554801)
            ·
              refine ⟨2764918614254886065666101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3686558152339848087554801 2764918614254886065666101)
              ·
                refine ⟨259211120086395568656197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2764918614254886065666101 259211120086395568656197)
                ·
                  refine ⟨48602085016199169123037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 259211120086395568656197 48602085016199169123037)
                  ·
                    rfl

theorem cell22_425935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 5, 4].length) (baseStart_425935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_425935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_425935 prefixEnd_425935 := by exact prefixLift 425935
  have htrace : WordTrace (prefixWord ++ tailWord_425935) baseStart_425935 baseEnd_425935 := by
    simpa [prefixWord, tailWord_425935, baseEnd_425935] using wordTrace_append hprefix tailTrace_425935
  have hstable : (prefixWord ++ tailWord_425935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425935).length < 2 ^ (prefixWord ++ tailWord_425935).sum := by decide
  have hdescent : baseEnd_425935 < baseStart_425935 := by decide
  rcases family_descends (prefixWord ++ tailWord_425935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425980 : List Nat := [2, 2, 2, 1, 2, 2, 5, 6]
def baseStart_425980 : Nat := 118140960795 + 425980 * 2 ^ 59
def prefixEnd_425980 : Nat := 4983230072969 + 3 ^ 40 * 425980 * 2
def baseEnd_425980 : Nat := 16202406607581376665997

theorem tailTrace_425980 : CollatzResearch.WordTrace tailWord_425980 prefixEnd_425980 16202406607581376665997 := by
  unfold tailWord_425980
  simp only [CollatzResearch.WordTrace]
  refine ⟨7768383498377343218529697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10357844664503124291372929 7768383498377343218529697)
  ·
    refine ⟨5826287623783007413897273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7768383498377343218529697 5826287623783007413897273)
    ·
      refine ⟨4369715717837255560422955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5826287623783007413897273 4369715717837255560422955)
      ·
        refine ⟨6554573576755883340634433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4369715717837255560422955 6554573576755883340634433)
        ·
          refine ⟨4915930182566912505475825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6554573576755883340634433 4915930182566912505475825)
          ·
            refine ⟨3686947636925184379106869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4915930182566912505475825 3686947636925184379106869)
            ·
              refine ⟨345651340961736035541269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3686947636925184379106869 345651340961736035541269)
              ·
                refine ⟨16202406607581376665997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 345651340961736035541269 16202406607581376665997)
                ·
                  rfl

theorem cell22_425980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 6].length) (baseStart_425980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_425980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_425980 prefixEnd_425980 := by exact prefixLift 425980
  have htrace : WordTrace (prefixWord ++ tailWord_425980) baseStart_425980 baseEnd_425980 := by
    simpa [prefixWord, tailWord_425980, baseEnd_425980] using wordTrace_append hprefix tailTrace_425980
  have hstable : (prefixWord ++ tailWord_425980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425980).length < 2 ^ (prefixWord ++ tailWord_425980).sum := by decide
  have hdescent : baseEnd_425980 < baseStart_425980 := by decide
  rcases family_descends (prefixWord ++ tailWord_425980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425982 : List Nat := [4, 2, 2, 2, 1, 2, 1, 1, 1, 6]
def baseStart_425982 : Nat := 118140960795 + 425982 * 2 ^ 59
def prefixEnd_425982 : Nat := 4983230072969 + 3 ^ 40 * 425982 * 2
def baseEnd_425982 : Nat := 145822344109105051443967

theorem tailTrace_425982 : CollatzResearch.WordTrace tailWord_425982 prefixEnd_425982 145822344109105051443967 := by
  unfold tailWord_425982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1942104992843430097329025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10357893295164960519088133 1942104992843430097329025)
  ·
    refine ⟨1456578744632572572996769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1942104992843430097329025 1456578744632572572996769)
    ·
      refine ⟨1092434058474429429747577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1456578744632572572996769 1092434058474429429747577)
      ·
        refine ⟨819325543855822072310683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1092434058474429429747577 819325543855822072310683)
        ·
          refine ⟨1228988315783733108466025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 819325543855822072310683 1228988315783733108466025)
          ·
            refine ⟨921741236837799831349519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1228988315783733108466025 921741236837799831349519)
            ·
              refine ⟨1382611855256699747024279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 921741236837799831349519 1382611855256699747024279)
              ·
                refine ⟨2073917782885049620536419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1382611855256699747024279 2073917782885049620536419)
                ·
                  refine ⟨3110876674327574430804629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2073917782885049620536419 3110876674327574430804629)
                  ·
                    refine ⟨145822344109105051443967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3110876674327574430804629 145822344109105051443967)
                    ·
                      rfl

theorem cell22_425982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_425982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_425982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_425982 prefixEnd_425982 := by exact prefixLift 425982
  have htrace : WordTrace (prefixWord ++ tailWord_425982) baseStart_425982 baseEnd_425982 := by
    simpa [prefixWord, tailWord_425982, baseEnd_425982] using wordTrace_append hprefix tailTrace_425982
  have hstable : (prefixWord ++ tailWord_425982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425982).length < 2 ^ (prefixWord ++ tailWord_425982).sum := by decide
  have hdescent : baseEnd_425982 < baseStart_425982 := by decide
  rcases family_descends (prefixWord ++ tailWord_425982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425988 : List Nat := [2, 3, 2, 4, 2, 1, 2, 1, 1, 4]
def baseStart_425988 : Nat := 118140960795 + 425988 * 2 ^ 59
def prefixEnd_425988 : Nat := 4983230072969 + 3 ^ 40 * 425988 * 2
def baseEnd_425988 : Nat := 145824398031723035793949

theorem tailTrace_425988 : CollatzResearch.WordTrace tailWord_425988 prefixEnd_425988 145824398031723035793949 := by
  unfold tailWord_425988
  simp only [CollatzResearch.WordTrace]
  refine ⟨7768529390362851901675309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10358039187150469202233745 7768529390362851901675309)
  ·
    refine ⟨2913198521386069463128241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7768529390362851901675309 2913198521386069463128241)
    ·
      refine ⟨2184898891039552097346181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2913198521386069463128241 2184898891039552097346181)
      ·
        refine ⟨409668542069916018252409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2184898891039552097346181 409668542069916018252409)
        ·
          refine ⟨307251406552437013689307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409668542069916018252409 307251406552437013689307)
          ·
            refine ⟨460877109828655520533961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307251406552437013689307 460877109828655520533961)
            ·
              refine ⟨345657832371491640400471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 460877109828655520533961 345657832371491640400471)
              ·
                refine ⟨518486748557237460600707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 345657832371491640400471 518486748557237460600707)
                ·
                  refine ⟨777730122835856190901061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 518486748557237460600707 777730122835856190901061)
                  ·
                    refine ⟨145824398031723035793949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 777730122835856190901061 145824398031723035793949)
                    ·
                      rfl

theorem cell22_425988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_425988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_425988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_425988 prefixEnd_425988 := by exact prefixLift 425988
  have htrace : WordTrace (prefixWord ++ tailWord_425988) baseStart_425988 baseEnd_425988 := by
    simpa [prefixWord, tailWord_425988, baseEnd_425988] using wordTrace_append hprefix tailTrace_425988
  have hstable : (prefixWord ++ tailWord_425988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425988).length < 2 ^ (prefixWord ++ tailWord_425988).sum := by decide
  have hdescent : baseEnd_425988 < baseStart_425988 := by decide
  rcases family_descends (prefixWord ++ tailWord_425988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_425995 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 5, 3]
def baseStart_425995 : Nat := 118140960795 + 425995 * 2 ^ 59
def prefixEnd_425995 : Nat := 4983230072969 + 3 ^ 40 * 425995 * 2
def baseEnd_425995 : Nat := 145826794274777350868927

theorem tailTrace_425995 : CollatzResearch.WordTrace tailWord_425995 prefixEnd_425995 145826794274777350868927 := by
  unfold tailWord_425995
  simp only [CollatzResearch.WordTrace]
  refine ⟨15537314091700343998855439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10358209394466895999236959 15537314091700343998855439)
  ·
    refine ⟨23305971137550515998283159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15537314091700343998855439 23305971137550515998283159)
    ·
      refine ⟨34958956706325773997424739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23305971137550515998283159 34958956706325773997424739)
      ·
        refine ⟨52438435059488660996137109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34958956706325773997424739 52438435059488660996137109)
        ·
          refine ⟨2458051643413530984193927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 52438435059488660996137109 2458051643413530984193927)
          ·
            refine ⟨3687077465120296476290891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2458051643413530984193927 3687077465120296476290891)
            ·
              refine ⟨5530616197680444714436337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3687077465120296476290891 5530616197680444714436337)
              ·
                refine ⟨4147962148260333535827253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5530616197680444714436337 4147962148260333535827253)
                ·
                  refine ⟨388871451399406268983805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4147962148260333535827253 388871451399406268983805)
                  ·
                    refine ⟨145826794274777350868927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 388871451399406268983805 145826794274777350868927)
                    ·
                      rfl

theorem cell22_425995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 5, 3].length) (baseStart_425995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_425995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_425995 prefixEnd_425995 := by exact prefixLift 425995
  have htrace : WordTrace (prefixWord ++ tailWord_425995) baseStart_425995 baseEnd_425995 := by
    simpa [prefixWord, tailWord_425995, baseEnd_425995] using wordTrace_append hprefix tailTrace_425995
  have hstable : (prefixWord ++ tailWord_425995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_425995).length < 2 ^ (prefixWord ++ tailWord_425995).sum := by decide
  have hdescent : baseEnd_425995 < baseStart_425995 := by decide
  rcases family_descends (prefixWord ++ tailWord_425995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426012 : List Nat := [2, 2, 3, 1, 3, 1, 1, 3, 3, 3]
def baseStart_426012 : Nat := 118140960795 + 426012 * 2 ^ 59
def prefixEnd_426012 : Nat := 4983230072969 + 3 ^ 40 * 426012 * 2
def baseEnd_426012 : Nat := 145832613722194973193875

theorem tailTrace_426012 : CollatzResearch.WordTrace tailWord_426012 prefixEnd_426012 145832613722194973193875 := by
  unfold tailWord_426012
  simp only [CollatzResearch.WordTrace]
  refine ⟨7768967066319377951112145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10358622755092503934816193 7768967066319377951112145)
  ·
    refine ⟨5826725299739533463334109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7768967066319377951112145 5826725299739533463334109)
    ·
      refine ⟨2185021987402325048750291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5826725299739533463334109 2185021987402325048750291)
      ·
        refine ⟨3277532981103487573125437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2185021987402325048750291 3277532981103487573125437)
        ·
          refine ⟨1229074867913807839922039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3277532981103487573125437 1229074867913807839922039)
          ·
            refine ⟨1843612301870711759883059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1229074867913807839922039 1843612301870711759883059)
            ·
              refine ⟨2765418452806067639824589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1843612301870711759883059 2765418452806067639824589)
              ·
                refine ⟨1037031919802275364934221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2765418452806067639824589 1037031919802275364934221)
                ·
                  refine ⟨388886969925853261850333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1037031919802275364934221 388886969925853261850333)
                  ·
                    refine ⟨145832613722194973193875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 388886969925853261850333 145832613722194973193875)
                    ·
                      rfl

theorem cell22_426012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_426012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_426012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_426012 prefixEnd_426012 := by exact prefixLift 426012
  have htrace : WordTrace (prefixWord ++ tailWord_426012) baseStart_426012 baseEnd_426012 := by
    simpa [prefixWord, tailWord_426012, baseEnd_426012] using wordTrace_append hprefix tailTrace_426012
  have hstable : (prefixWord ++ tailWord_426012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426012).length < 2 ^ (prefixWord ++ tailWord_426012).sum := by decide
  have hdescent : baseEnd_426012 < baseStart_426012 := by decide
  rcases family_descends (prefixWord ++ tailWord_426012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426102 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 3, 5]
def baseStart_426102 : Nat := 118140960795 + 426102 * 2 ^ 59
def prefixEnd_426102 : Nat := 4983230072969 + 3 ^ 40 * 426102 * 2
def baseEnd_426102 : Nat := 145863422561464738443599

theorem tailTrace_426102 : CollatzResearch.WordTrace tailWord_426102 prefixEnd_426102 145863422561464738443599 := by
  unfold tailWord_426102
  simp only [CollatzResearch.WordTrace]
  refine ⟨971326043894543829562535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10360811134875134182000373 971326043894543829562535)
  ·
    refine ⟨1456989065841815744343803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 971326043894543829562535 1456989065841815744343803)
    ·
      refine ⟨2185483598762723616515705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1456989065841815744343803 2185483598762723616515705)
      ·
        refine ⟨1639112699072042712386779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2185483598762723616515705 1639112699072042712386779)
        ·
          refine ⟨2458669048608064068580169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1639112699072042712386779 2458669048608064068580169)
          ·
            refine ⟨1844001786456048051435127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2458669048608064068580169 1844001786456048051435127)
            ·
              refine ⟨2766002679684072077152691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1844001786456048051435127 2766002679684072077152691)
              ·
                refine ⟨4149004019526108115729037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2766002679684072077152691 4149004019526108115729037)
                ·
                  refine ⟨1555876507322290543398389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4149004019526108115729037 1555876507322290543398389)
                  ·
                    refine ⟨145863422561464738443599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1555876507322290543398389 145863422561464738443599)
                    ·
                      rfl

theorem cell22_426102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_426102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_426102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_426102 prefixEnd_426102 := by exact prefixLift 426102
  have htrace : WordTrace (prefixWord ++ tailWord_426102) baseStart_426102 baseEnd_426102 := by
    simpa [prefixWord, tailWord_426102, baseEnd_426102] using wordTrace_append hprefix tailTrace_426102
  have hstable : (prefixWord ++ tailWord_426102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426102).length < 2 ^ (prefixWord ++ tailWord_426102).sum := by decide
  have hdescent : baseEnd_426102 < baseStart_426102 := by decide
  rcases family_descends (prefixWord ++ tailWord_426102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426117 : List Nat := [1, 3, 1, 1, 5, 1, 2, 2, 2, 4]
def baseStart_426117 : Nat := 118140960795 + 426117 * 2 ^ 59
def prefixEnd_426117 : Nat := 4983230072969 + 3 ^ 40 * 426117 * 2
def baseEnd_426117 : Nat := 145868557368009699318553

theorem tailTrace_426117 : CollatzResearch.WordTrace tailWord_426117 prefixEnd_426117 145868557368009699318553 := by
  unfold tailWord_426117
  simp only [CollatzResearch.WordTrace]
  refine ⟨15541763797258358834796605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10361175864838905889864403 15541763797258358834796605)
  ·
    refine ⟨5828161423971884563048727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15541763797258358834796605 5828161423971884563048727)
    ·
      refine ⟨8742242135957826844573091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5828161423971884563048727 8742242135957826844573091)
      ·
        refine ⟨13113363203936740266859637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8742242135957826844573091 13113363203936740266859637)
        ·
          refine ⟨1229377800369069400018091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13113363203936740266859637 1229377800369069400018091)
          ·
            refine ⟨1844066700553604100027137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1229377800369069400018091 1844066700553604100027137)
            ·
              refine ⟨1383050025415203075020353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1844066700553604100027137 1383050025415203075020353)
              ·
                refine ⟨1037287519061402306265265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1383050025415203075020353 1037287519061402306265265)
                ·
                  refine ⟨777965639296051729698949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1037287519061402306265265 777965639296051729698949)
                  ·
                    refine ⟨145868557368009699318553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 777965639296051729698949 145868557368009699318553)
                    ·
                      rfl

theorem cell22_426117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_426117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_426117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_426117 prefixEnd_426117 := by exact prefixLift 426117
  have htrace : WordTrace (prefixWord ++ tailWord_426117) baseStart_426117 baseEnd_426117 := by
    simpa [prefixWord, tailWord_426117, baseEnd_426117] using wordTrace_append hprefix tailTrace_426117
  have hstable : (prefixWord ++ tailWord_426117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426117).length < 2 ^ (prefixWord ++ tailWord_426117).sum := by decide
  have hdescent : baseEnd_426117 < baseStart_426117 := by decide
  rcases family_descends (prefixWord ++ tailWord_426117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426151 : List Nat := [1, 1, 6, 2, 2, 2, 1, 1, 2, 4]
def baseStart_426151 : Nat := 118140960795 + 426151 * 2 ^ 59
def prefixEnd_426151 : Nat := 4983230072969 + 3 ^ 40 * 426151 * 2
def baseEnd_426151 : Nat := 145880196262844943968449

theorem tailTrace_426151 : CollatzResearch.WordTrace tailWord_426151 prefixEnd_426151 145880196262844943968449 := by
  unfold tailWord_426151
  simp only [CollatzResearch.WordTrace]
  refine ⟨15543003879135182641534307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10362002586090121761022871 15543003879135182641534307)
  ·
    refine ⟨23314505818702773962301461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15543003879135182641534307 23314505818702773962301461)
    ·
      refine ⟨1092867460251692529482881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23314505818702773962301461 1092867460251692529482881)
      ·
        refine ⟨819650595188769397112161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1092867460251692529482881 819650595188769397112161)
        ·
          refine ⟨614737946391577047834121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 819650595188769397112161 614737946391577047834121)
          ·
            refine ⟨461053459793682785875591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 614737946391577047834121 461053459793682785875591)
            ·
              refine ⟨691580189690524178813387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461053459793682785875591 691580189690524178813387)
              ·
                refine ⟨1037370284535786268220081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 691580189690524178813387 1037370284535786268220081)
                ·
                  refine ⟨778027713401839701165061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1037370284535786268220081 778027713401839701165061)
                  ·
                    refine ⟨145880196262844943968449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 778027713401839701165061 145880196262844943968449)
                    ·
                      rfl

theorem cell22_426151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_426151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_426151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_426151 prefixEnd_426151 := by exact prefixLift 426151
  have htrace : WordTrace (prefixWord ++ tailWord_426151) baseStart_426151 baseEnd_426151 := by
    simpa [prefixWord, tailWord_426151, baseEnd_426151] using wordTrace_append hprefix tailTrace_426151
  have hstable : (prefixWord ++ tailWord_426151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426151).length < 2 ^ (prefixWord ++ tailWord_426151).sum := by decide
  have hdescent : baseEnd_426151 < baseStart_426151 := by decide
  rcases family_descends (prefixWord ++ tailWord_426151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426235 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 2, 10]
def baseStart_426235 : Nat := 118140960795 + 426235 * 2 ^ 59
def prefixEnd_426235 : Nat := 4983230072969 + 3 ^ 40 * 426235 * 2
def baseEnd_426235 : Nat := 145908951179496724868191

theorem tailTrace_426235 : CollatzResearch.WordTrace tailWord_426235 prefixEnd_426235 145908951179496724868191 := by
  unfold tailWord_426235
  simp only [CollatzResearch.WordTrace]
  refine ⟨15546067610830864987592159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10364045073887243325061439 15546067610830864987592159)
  ·
    refine ⟨23319101416246297481388239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15546067610830864987592159 23319101416246297481388239)
    ·
      refine ⟨34978652124369446222082359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23319101416246297481388239 34978652124369446222082359)
      ·
        refine ⟨52467978186554169333123539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34978652124369446222082359 52467978186554169333123539)
        ·
          refine ⟨78701967279831253999685309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52467978186554169333123539 78701967279831253999685309)
          ·
            refine ⟨29513237729936720249881991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78701967279831253999685309 29513237729936720249881991)
            ·
              refine ⟨44269856594905080374822987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29513237729936720249881991 44269856594905080374822987)
              ·
                refine ⟨66404784892357620562234481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44269856594905080374822987 66404784892357620562234481)
                ·
                  refine ⟨49803588669268215421675861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66404784892357620562234481 49803588669268215421675861)
                  ·
                    refine ⟨145908951179496724868191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 49803588669268215421675861 145908951179496724868191)
                    ·
                      rfl

theorem cell22_426235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 10].length) (baseStart_426235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_426235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_426235 prefixEnd_426235 := by exact prefixLift 426235
  have htrace : WordTrace (prefixWord ++ tailWord_426235) baseStart_426235 baseEnd_426235 := by
    simpa [prefixWord, tailWord_426235, baseEnd_426235] using wordTrace_append hprefix tailTrace_426235
  have hstable : (prefixWord ++ tailWord_426235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426235).length < 2 ^ (prefixWord ++ tailWord_426235).sum := by decide
  have hdescent : baseEnd_426235 < baseStart_426235 := by decide
  rcases family_descends (prefixWord ++ tailWord_426235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426252 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 4, 4]
def baseStart_426252 : Nat := 118140960795 + 426252 * 2 ^ 59
def prefixEnd_426252 : Nat := 4983230072969 + 3 ^ 40 * 426252 * 2
def baseEnd_426252 : Nat := 145914770626914347193139

theorem tailTrace_426252 : CollatzResearch.WordTrace tailWord_426252 prefixEnd_426252 145914770626914347193139 := by
  unfold tailWord_426252
  simp only [CollatzResearch.WordTrace]
  refine ⟨7773343825884638445480505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10364458434512851260640673 7773343825884638445480505)
  ·
    refine ⟨5830007869413478834110379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7773343825884638445480505 5830007869413478834110379)
    ·
      refine ⟨8745011804120218251165569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5830007869413478834110379 8745011804120218251165569)
      ·
        refine ⟨6558758853090163688374177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8745011804120218251165569 6558758853090163688374177)
        ·
          refine ⟨4919069139817622766280633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6558758853090163688374177 4919069139817622766280633)
          ·
            refine ⟨3689301854863217074710475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4919069139817622766280633 3689301854863217074710475)
            ·
              refine ⟨5533952782294825612065713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3689301854863217074710475 5533952782294825612065713)
              ·
                refine ⟨4150464586721119209049285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5533952782294825612065713 4150464586721119209049285)
                ·
                  refine ⟨778212110010209851696741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4150464586721119209049285 778212110010209851696741)
                  ·
                    refine ⟨145914770626914347193139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 778212110010209851696741 145914770626914347193139)
                    ·
                      rfl

theorem cell22_426252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_426252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_426252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_426252 prefixEnd_426252 := by exact prefixLift 426252
  have htrace : WordTrace (prefixWord ++ tailWord_426252) baseStart_426252 baseEnd_426252 := by
    simpa [prefixWord, tailWord_426252, baseEnd_426252] using wordTrace_append hprefix tailTrace_426252
  have hstable : (prefixWord ++ tailWord_426252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426252).length < 2 ^ (prefixWord ++ tailWord_426252).sum := by decide
  have hdescent : baseEnd_426252 < baseStart_426252 := by decide
  rcases family_descends (prefixWord ++ tailWord_426252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426290 : List Nat := [3, 2, 1, 1, 6, 1, 2, 2, 4]
def baseStart_426290 : Nat := 118140960795 + 426290 * 2 ^ 59
def prefixEnd_426290 : Nat := 4983230072969 + 3 ^ 40 * 426290 * 2
def baseEnd_426290 : Nat := 48642592934498304914341

theorem tailTrace_426290 : CollatzResearch.WordTrace tailWord_426290 prefixEnd_426290 48642592934498304914341 := by
  unfold tailWord_426290
  simp only [CollatzResearch.WordTrace]
  refine ⟨3887018406407902345211081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10365382417087739587229549 3887018406407902345211081)
  ·
    refine ⟨2915263804805926758908311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3887018406407902345211081 2915263804805926758908311)
    ·
      refine ⟨4372895707208890138362467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2915263804805926758908311 4372895707208890138362467)
      ·
        refine ⟨6559343560813335207543701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4372895707208890138362467 6559343560813335207543701)
        ·
          refine ⟨307469229413125087853611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6559343560813335207543701 307469229413125087853611)
          ·
            refine ⟨461203844119687631780417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307469229413125087853611 461203844119687631780417)
            ·
              refine ⟨345902883089765723835313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 461203844119687631780417 345902883089765723835313)
              ·
                refine ⟨259427162317324292876485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 345902883089765723835313 259427162317324292876485)
                ·
                  refine ⟨48642592934498304914341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 259427162317324292876485 48642592934498304914341)
                  ·
                    rfl

theorem cell22_426290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_426290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_426290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_426290 prefixEnd_426290 := by exact prefixLift 426290
  have htrace : WordTrace (prefixWord ++ tailWord_426290) baseStart_426290 baseEnd_426290 := by
    simpa [prefixWord, tailWord_426290, baseEnd_426290] using wordTrace_append hprefix tailTrace_426290
  have hstable : (prefixWord ++ tailWord_426290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426290).length < 2 ^ (prefixWord ++ tailWord_426290).sum := by decide
  have hdescent : baseEnd_426290 < baseStart_426290 := by decide
  rcases family_descends (prefixWord ++ tailWord_426290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426327 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 1, 7]
def baseStart_426327 : Nat := 118140960795 + 426327 * 2 ^ 59
def prefixEnd_426327 : Nat := 4983230072969 + 3 ^ 40 * 426327 * 2
def baseEnd_426327 : Nat := 145940444659639151567909

theorem tailTrace_426327 : CollatzResearch.WordTrace tailWord_426327 prefixEnd_426327 145940444659639151567909 := by
  unfold tailWord_426327
  simp only [CollatzResearch.WordTrace]
  refine ⟨15549423126497564699941235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10366282084331709799960823 15549423126497564699941235)
  ·
    refine ⟨23324134689746347049911853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15549423126497564699941235 23324134689746347049911853)
    ·
      refine ⟨8746550508654880143716945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23324134689746347049911853 8746550508654880143716945)
      ·
        refine ⟨6559912881491160107787709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8746550508654880143716945 6559912881491160107787709)
        ·
          refine ⟨2459967330559185040420391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6559912881491160107787709 2459967330559185040420391)
          ·
            refine ⟨3689950995838777560630587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2459967330559185040420391 3689950995838777560630587)
            ·
              refine ⟨5534926493758166340945881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3689950995838777560630587 5534926493758166340945881)
              ·
                refine ⟨4151194870318624755709411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5534926493758166340945881 4151194870318624755709411)
                ·
                  refine ⟨6226792305477937133564117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4151194870318624755709411 6226792305477937133564117)
                  ·
                    refine ⟨145940444659639151567909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6226792305477937133564117 145940444659639151567909)
                    ·
                      rfl

theorem cell22_426327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_426327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_426327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_426327 prefixEnd_426327 := by exact prefixLift 426327
  have htrace : WordTrace (prefixWord ++ tailWord_426327) baseStart_426327 baseEnd_426327 := by
    simpa [prefixWord, tailWord_426327, baseEnd_426327] using wordTrace_append hprefix tailTrace_426327
  have hstable : (prefixWord ++ tailWord_426327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426327).length < 2 ^ (prefixWord ++ tailWord_426327).sum := by decide
  have hdescent : baseEnd_426327 < baseStart_426327 := by decide
  rcases family_descends (prefixWord ++ tailWord_426327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426344 : List Nat := [2, 1, 4, 2, 2, 1, 1, 2, 2, 5]
def baseStart_426344 : Nat := 118140960795 + 426344 * 2 ^ 59
def prefixEnd_426344 : Nat := 4983230072969 + 3 ^ 40 * 426344 * 2
def baseEnd_426344 : Nat := 145946264107056773892857

theorem tailTrace_426344 : CollatzResearch.WordTrace tailWord_426344 prefixEnd_426344 145946264107056773892857 := by
  unfold tailWord_426344
  simp only [CollatzResearch.WordTrace]
  refine ⟨7775021583717988301655043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10366695444957317735540057 7775021583717988301655043)
  ·
    refine ⟨11662532375576982452482565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7775021583717988301655043 11662532375576982452482565)
    ·
      refine ⟨2186724820420684209840481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11662532375576982452482565 2186724820420684209840481)
      ·
        refine ⟨1640043615315513157380361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2186724820420684209840481 1640043615315513157380361)
        ·
          refine ⟨1230032711486634868035271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1640043615315513157380361 1230032711486634868035271)
          ·
            refine ⟨1845049067229952302052907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1230032711486634868035271 1845049067229952302052907)
            ·
              refine ⟨2767573600844928453079361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1845049067229952302052907 2767573600844928453079361)
              ·
                refine ⟨2075680200633696339809521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2767573600844928453079361 2075680200633696339809521)
                ·
                  refine ⟨1556760150475272254857141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2075680200633696339809521 1556760150475272254857141)
                  ·
                    refine ⟨145946264107056773892857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1556760150475272254857141 145946264107056773892857)
                    ·
                      rfl

theorem cell22_426344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_426344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_426344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_426344 prefixEnd_426344 := by exact prefixLift 426344
  have htrace : WordTrace (prefixWord ++ tailWord_426344) baseStart_426344 baseEnd_426344 := by
    simpa [prefixWord, tailWord_426344, baseEnd_426344] using wordTrace_append hprefix tailTrace_426344
  have hstable : (prefixWord ++ tailWord_426344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426344).length < 2 ^ (prefixWord ++ tailWord_426344).sum := by decide
  have hdescent : baseEnd_426344 < baseStart_426344 := by decide
  rcases family_descends (prefixWord ++ tailWord_426344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426346 : List Nat := [3, 1, 3, 3, 1, 1, 3, 2, 5]
def baseStart_426346 : Nat := 118140960795 + 426346 * 2 ^ 59
def prefixEnd_426346 : Nat := 4983230072969 + 3 ^ 40 * 426346 * 2
def baseEnd_426346 : Nat := 48648982915976478447617

theorem tailTrace_426346 : CollatzResearch.WordTrace tailWord_426346 prefixEnd_426346 48648982915976478447617 := by
  unfold tailWord_426346
  simp only [CollatzResearch.WordTrace]
  refine ⟨3887529028357182736220723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10366744075619153963255261 3887529028357182736220723)
  ·
    refine ⟨5831293542535774104331085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3887529028357182736220723 5831293542535774104331085)
    ·
      refine ⟨2186735078450915289124157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5831293542535774104331085 2186735078450915289124157)
      ·
        refine ⟨820025654419093233421559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2186735078450915289124157 820025654419093233421559)
        ·
          refine ⟨1230038481628639850132339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 820025654419093233421559 1230038481628639850132339)
          ·
            refine ⟨1845057722442959775198509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1230038481628639850132339 1845057722442959775198509)
            ·
              refine ⟨691896645916109915699441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1845057722442959775198509 691896645916109915699441)
              ·
                refine ⟨518922484437082436774581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 691896645916109915699441 518922484437082436774581)
                ·
                  refine ⟨48648982915976478447617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 518922484437082436774581 48648982915976478447617)
                  ·
                    rfl

theorem cell22_426346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 5].length) (baseStart_426346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_426346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_426346 prefixEnd_426346 := by exact prefixLift 426346
  have htrace : WordTrace (prefixWord ++ tailWord_426346) baseStart_426346 baseEnd_426346 := by
    simpa [prefixWord, tailWord_426346, baseEnd_426346] using wordTrace_append hprefix tailTrace_426346
  have hstable : (prefixWord ++ tailWord_426346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426346).length < 2 ^ (prefixWord ++ tailWord_426346).sum := by decide
  have hdescent : baseEnd_426346 < baseStart_426346 := by decide
  rcases family_descends (prefixWord ++ tailWord_426346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426376 : List Nat := [2, 1, 3, 3, 1, 1, 4, 2, 1, 4]
def baseStart_426376 : Nat := 118140960795 + 426376 * 2 ^ 59
def prefixEnd_426376 : Nat := 4983230072969 + 3 ^ 40 * 426376 * 2
def baseEnd_426376 : Nat := 145957218361019357092759

theorem tailTrace_426376 : CollatzResearch.WordTrace tailWord_426376 prefixEnd_426376 145957218361019357092759 := by
  unfold tailWord_426376
  simp only [CollatzResearch.WordTrace]
  refine ⟨7775605151660023034237491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10367473535546697378983321 7775605151660023034237491)
  ·
    refine ⟨11663407727490034551356237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7775605151660023034237491 11663407727490034551356237)
    ·
      refine ⟨4373777897808762956758589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11663407727490034551356237 4373777897808762956758589)
      ·
        refine ⟨1640166711678286108784471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4373777897808762956758589 1640166711678286108784471)
        ·
          refine ⟨2460250067517429163176707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1640166711678286108784471 2460250067517429163176707)
          ·
            refine ⟨3690375101276143744765061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2460250067517429163176707 3690375101276143744765061)
            ·
              refine ⟨691945331489276952143449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3690375101276143744765061 691945331489276952143449)
              ·
                refine ⟨518958998616957714107587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 691945331489276952143449 518958998616957714107587)
                ·
                  refine ⟨778438497925436571161381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 518958998616957714107587 778438497925436571161381)
                  ·
                    refine ⟨145957218361019357092759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 778438497925436571161381 145957218361019357092759)
                    ·
                      rfl

theorem cell22_426376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_426376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_426376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_426376 prefixEnd_426376 := by exact prefixLift 426376
  have htrace : WordTrace (prefixWord ++ tailWord_426376) baseStart_426376 baseEnd_426376 := by
    simpa [prefixWord, tailWord_426376, baseEnd_426376] using wordTrace_append hprefix tailTrace_426376
  have hstable : (prefixWord ++ tailWord_426376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426376).length < 2 ^ (prefixWord ++ tailWord_426376).sum := by decide
  have hdescent : baseEnd_426376 < baseStart_426376 := by decide
  rcases family_descends (prefixWord ++ tailWord_426376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426391 : List Nat := [1, 1, 3, 3, 1, 1, 5, 3, 4]
def baseStart_426391 : Nat := 118140960795 + 426391 * 2 ^ 59
def prefixEnd_426391 : Nat := 4983230072969 + 3 ^ 40 * 426391 * 2
def baseEnd_426391 : Nat := 48654117722521439322571

theorem tailTrace_426391 : CollatzResearch.WordTrace tailWord_426391 prefixEnd_426391 48654117722521439322571 := by
  unfold tailWord_426391
  simp only [CollatzResearch.WordTrace]
  refine ⟨15551757398265703630271027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10367838265510469086847351 15551757398265703630271027)
  ·
    refine ⟨23327636097398555445406541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15551757398265703630271027 23327636097398555445406541)
    ·
      refine ⟨8747863536524458292027453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23327636097398555445406541 8747863536524458292027453)
      ·
        refine ⟨3280448826196671859510295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8747863536524458292027453 3280448826196671859510295)
        ·
          refine ⟨4920673239295007789265443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3280448826196671859510295 4920673239295007789265443)
          ·
            refine ⟨7381009858942511683898165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4920673239295007789265443 7381009858942511683898165)
            ·
              refine ⟨691969674275860470365453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7381009858942511683898165 691969674275860470365453)
              ·
                refine ⟨259488627853447676387045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 691969674275860470365453 259488627853447676387045)
                ·
                  refine ⟨48654117722521439322571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 259488627853447676387045 48654117722521439322571)
                  ·
                    rfl

theorem cell22_426391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 3, 4].length) (baseStart_426391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_426391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_426391 prefixEnd_426391 := by exact prefixLift 426391
  have htrace : WordTrace (prefixWord ++ tailWord_426391) baseStart_426391 baseEnd_426391 := by
    simpa [prefixWord, tailWord_426391, baseEnd_426391] using wordTrace_append hprefix tailTrace_426391
  have hstable : (prefixWord ++ tailWord_426391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426391).length < 2 ^ (prefixWord ++ tailWord_426391).sum := by decide
  have hdescent : baseEnd_426391 < baseStart_426391 := by decide
  rcases family_descends (prefixWord ++ tailWord_426391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426404 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 4, 4]
def baseStart_426404 : Nat := 118140960795 + 426404 * 2 ^ 59
def prefixEnd_426404 : Nat := 4983230072969 + 3 ^ 40 * 426404 * 2
def baseEnd_426404 : Nat := 145966803333236617392673

theorem tailTrace_426404 : CollatzResearch.WordTrace tailWord_426404 prefixEnd_426404 145966803333236617392673 := by
  unfold tailWord_426404
  simp only [CollatzResearch.WordTrace]
  refine ⟨7776115773609303425247133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10368154364812404566996177 7776115773609303425247133)
  ·
    refine ⟨2916043415103488784467675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7776115773609303425247133 2916043415103488784467675)
    ·
      refine ⟨4374065122655233176701513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2916043415103488784467675 4374065122655233176701513)
      ·
        refine ⟨3280548841991424882526135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4374065122655233176701513 3280548841991424882526135)
        ·
          refine ⟨4920823262987137323789203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3280548841991424882526135 4920823262987137323789203)
          ·
            refine ⟨7381234894480705985683805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4920823262987137323789203 7381234894480705985683805)
            ·
              refine ⟨2767963085430264744631427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7381234894480705985683805 2767963085430264744631427)
              ·
                refine ⟨4151944628145397116947141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2767963085430264744631427 4151944628145397116947141)
                ·
                  refine ⟨778489617777261959427589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4151944628145397116947141 778489617777261959427589)
                  ·
                    refine ⟨145966803333236617392673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 778489617777261959427589 145966803333236617392673)
                    ·
                      rfl

theorem cell22_426404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_426404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_426404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_426404 prefixEnd_426404 := by exact prefixLift 426404
  have htrace : WordTrace (prefixWord ++ tailWord_426404) baseStart_426404 baseEnd_426404 := by
    simpa [prefixWord, tailWord_426404, baseEnd_426404] using wordTrace_append hprefix tailTrace_426404
  have hstable : (prefixWord ++ tailWord_426404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426404).length < 2 ^ (prefixWord ++ tailWord_426404).sum := by decide
  have hdescent : baseEnd_426404 < baseStart_426404 := by decide
  rcases family_descends (prefixWord ++ tailWord_426404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426408 : List Nat := [2, 1, 6, 1, 1, 3, 1, 1, 6]
def baseStart_426408 : Nat := 118140960795 + 426408 * 2 ^ 59
def prefixEnd_426408 : Nat := 4983230072969 + 3 ^ 40 * 426408 * 2
def baseEnd_426408 : Nat := 48656057538327313430887

theorem tailTrace_426408 : CollatzResearch.WordTrace tailWord_426408 prefixEnd_426408 48656057538327313430887 := by
  unfold tailWord_426408
  simp only [CollatzResearch.WordTrace]
  refine ⟨7776188719602057766819939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10368251626136077022426585 7776188719602057766819939)
  ·
    refine ⟨11664283079403086650229909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7776188719602057766819939 11664283079403086650229909)
    ·
      refine ⟨546763269347019686729527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11664283079403086650229909 546763269347019686729527)
      ·
        refine ⟨820144904020529530094291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546763269347019686729527 820144904020529530094291)
        ·
          refine ⟨1230217356030794295141437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 820144904020529530094291 1230217356030794295141437)
          ·
            refine ⟨461331508511547860678039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1230217356030794295141437 461331508511547860678039)
            ·
              refine ⟨691997262767321791017059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461331508511547860678039 691997262767321791017059)
              ·
                refine ⟨1037995894150982686525589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 691997262767321791017059 1037995894150982686525589)
                ·
                  refine ⟨48656057538327313430887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1037995894150982686525589 48656057538327313430887)
                  ·
                    rfl

theorem cell22_426408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 1, 6].length) (baseStart_426408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_426408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_426408 prefixEnd_426408 := by exact prefixLift 426408
  have htrace : WordTrace (prefixWord ++ tailWord_426408) baseStart_426408 baseEnd_426408 := by
    simpa [prefixWord, tailWord_426408, baseEnd_426408] using wordTrace_append hprefix tailTrace_426408
  have hstable : (prefixWord ++ tailWord_426408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426408).length < 2 ^ (prefixWord ++ tailWord_426408).sum := by decide
  have hdescent : baseEnd_426408 < baseStart_426408 := by decide
  rcases family_descends (prefixWord ++ tailWord_426408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426423 : List Nat := [1, 1, 3, 1, 3, 3, 4, 1, 2, 3]
def baseStart_426423 : Nat := 118140960795 + 426423 * 2 ^ 59
def prefixEnd_426423 : Nat := 4983230072969 + 3 ^ 40 * 426423 * 2
def baseEnd_426423 : Nat := 145973307421526901167615

theorem tailTrace_426423 : CollatzResearch.WordTrace tailWord_426423 prefixEnd_426423 145973307421526901167615 := by
  unfold tailWord_426423
  simp only [CollatzResearch.WordTrace]
  refine ⟨15552924534149773095435923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10368616356099848730290615 15552924534149773095435923)
  ·
    refine ⟨23329386801224659643153885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15552924534149773095435923 23329386801224659643153885)
    ·
      refine ⟨8748520050459247366182707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23329386801224659643153885 8748520050459247366182707)
      ·
        refine ⟨13122780075688871049274061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8748520050459247366182707 13122780075688871049274061)
        ·
          refine ⟨4921042528383326643477773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13122780075688871049274061 4921042528383326643477773)
          ·
            refine ⟨1845390948143747491304165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4921042528383326643477773 1845390948143747491304165)
            ·
              refine ⟨346010802776952654619531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1845390948143747491304165 346010802776952654619531)
              ·
                refine ⟨519016204165428981929297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 346010802776952654619531 519016204165428981929297)
                ·
                  refine ⟨389262153124071736446973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 519016204165428981929297 389262153124071736446973)
                  ·
                    refine ⟨145973307421526901167615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 389262153124071736446973 145973307421526901167615)
                    ·
                      rfl

theorem cell22_426423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 2, 3].length) (baseStart_426423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_426423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_426423 prefixEnd_426423 := by exact prefixLift 426423
  have htrace : WordTrace (prefixWord ++ tailWord_426423) baseStart_426423 baseEnd_426423 := by
    simpa [prefixWord, tailWord_426423, baseEnd_426423] using wordTrace_append hprefix tailTrace_426423
  have hstable : (prefixWord ++ tailWord_426423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426423).length < 2 ^ (prefixWord ++ tailWord_426423).sum := by decide
  have hdescent : baseEnd_426423 < baseStart_426423 := by decide
  rcases family_descends (prefixWord ++ tailWord_426423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426485 : List Nat := [1, 3, 5, 1, 2, 1, 1, 2, 3, 3]
def baseStart_426485 : Nat := 118140960795 + 426485 * 2 ^ 59
def prefixEnd_426485 : Nat := 4983230072969 + 3 ^ 40 * 426485 * 2
def baseEnd_426485 : Nat := 145994531288579406117425

theorem tailTrace_426485 : CollatzResearch.WordTrace tailWord_426485 prefixEnd_426485 145994531288579406117425 := by
  unfold tailWord_426485
  simp only [CollatzResearch.WordTrace]
  refine ⟨15555185859925157684192909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10370123906616771789461939 15555185859925157684192909)
  ·
    refine ⟨5833194697471934131572341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15555185859925157684192909 5833194697471934131572341)
    ·
      refine ⟨546862002887993824834907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5833194697471934131572341 546862002887993824834907)
      ·
        refine ⟨820293004331990737252361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546862002887993824834907 820293004331990737252361)
        ·
          refine ⟨615219753248993052939271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 820293004331990737252361 615219753248993052939271)
          ·
            refine ⟨922829629873489579408907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615219753248993052939271 922829629873489579408907)
            ·
              refine ⟨1384244444810234369113361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 922829629873489579408907 1384244444810234369113361)
              ·
                refine ⟨1038183333607675776835021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1384244444810234369113361 1038183333607675776835021)
                ·
                  refine ⟨389318750102878416313133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1038183333607675776835021 389318750102878416313133)
                  ·
                    refine ⟨145994531288579406117425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 389318750102878416313133 145994531288579406117425)
                    ·
                      rfl

theorem cell22_426485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_426485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_426485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_426485 prefixEnd_426485 := by exact prefixLift 426485
  have htrace : WordTrace (prefixWord ++ tailWord_426485) baseStart_426485 baseEnd_426485 := by
    simpa [prefixWord, tailWord_426485, baseEnd_426485] using wordTrace_append hprefix tailTrace_426485
  have hstable : (prefixWord ++ tailWord_426485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426485).length < 2 ^ (prefixWord ++ tailWord_426485).sum := by decide
  have hdescent : baseEnd_426485 < baseStart_426485 := by decide
  rcases family_descends (prefixWord ++ tailWord_426485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426556 : List Nat := [2, 2, 2, 2, 3, 1, 2, 1, 1, 6]
def baseStart_426556 : Nat := 118140960795 + 426556 * 2 ^ 59
def prefixEnd_426556 : Nat := 4983230072969 + 3 ^ 40 * 426556 * 2
def baseEnd_426556 : Nat := 146018836039558887592207

theorem tailTrace_426556 : CollatzResearch.WordTrace tailWord_426556 prefixEnd_426556 146018836039558887592207 := by
  unfold tailWord_426556
  simp only [CollatzResearch.WordTrace]
  refine ⟨7778887721333968405013761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10371850295111957873351681 7778887721333968405013761)
  ·
    refine ⟨5834165791000476303760321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7778887721333968405013761 5834165791000476303760321)
    ·
      refine ⟨4375624343250357227820241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5834165791000476303760321 4375624343250357227820241)
      ·
        refine ⟨3281718257437767920865181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4375624343250357227820241 3281718257437767920865181)
        ·
          refine ⟨1230644346539162970324443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3281718257437767920865181 1230644346539162970324443)
          ·
            refine ⟨1845966519808744455486665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1230644346539162970324443 1845966519808744455486665)
            ·
              refine ⟨1384474889856558341614999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1845966519808744455486665 1384474889856558341614999)
              ·
                refine ⟨2076712334784837512422499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1384474889856558341614999 2076712334784837512422499)
                ·
                  refine ⟨3115068502177256268633749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2076712334784837512422499 3115068502177256268633749)
                  ·
                    refine ⟨146018836039558887592207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3115068502177256268633749 146018836039558887592207)
                    ·
                      rfl

theorem cell22_426556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_426556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_426556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_426556 prefixEnd_426556 := by exact prefixLift 426556
  have htrace : WordTrace (prefixWord ++ tailWord_426556) baseStart_426556 baseEnd_426556 := by
    simpa [prefixWord, tailWord_426556, baseEnd_426556] using wordTrace_append hprefix tailTrace_426556
  have hstable : (prefixWord ++ tailWord_426556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426556).length < 2 ^ (prefixWord ++ tailWord_426556).sum := by decide
  have hdescent : baseEnd_426556 < baseStart_426556 := by decide
  rcases family_descends (prefixWord ++ tailWord_426556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426573 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_426573 : Nat := 118140960795 + 426573 * 2 ^ 59
def prefixEnd_426573 : Nat := 4983230072969 + 3 ^ 40 * 426573 * 2
def baseEnd_426573 : Nat := 146024655486976509917155

theorem tailTrace_426573 : CollatzResearch.WordTrace tailWord_426573 prefixEnd_426573 146024655486976509917155 := by
  unfold tailWord_426573
  simp only [CollatzResearch.WordTrace]
  refine ⟨15558395483606348713396373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10372263655737565808930915 15558395483606348713396373)
  ·
    refine ⟨729299788294047595940455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15558395483606348713396373 729299788294047595940455)
    ·
      refine ⟨1093949682441071393910683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 729299788294047595940455 1093949682441071393910683)
      ·
        refine ⟨1640924523661607090866025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1093949682441071393910683 1640924523661607090866025)
        ·
          refine ⟨1230693392746205318149519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1640924523661607090866025 1230693392746205318149519)
          ·
            refine ⟨1846040089119307977224279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1230693392746205318149519 1846040089119307977224279)
            ·
              refine ⟨2769060133678961965836419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1846040089119307977224279 2769060133678961965836419)
              ·
                refine ⟨4153590200518442948754629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2769060133678961965836419 4153590200518442948754629)
                ·
                  refine ⟨778798162597208052891493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4153590200518442948754629 778798162597208052891493)
                  ·
                    refine ⟨146024655486976509917155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 778798162597208052891493 146024655486976509917155)
                    ·
                      rfl

theorem cell22_426573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_426573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_426573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_426573 prefixEnd_426573 := by exact prefixLift 426573
  have htrace : WordTrace (prefixWord ++ tailWord_426573) baseStart_426573 baseEnd_426573 := by
    simpa [prefixWord, tailWord_426573, baseEnd_426573] using wordTrace_append hprefix tailTrace_426573
  have hstable : (prefixWord ++ tailWord_426573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426573).length < 2 ^ (prefixWord ++ tailWord_426573).sum := by decide
  have hdescent : baseEnd_426573 < baseStart_426573 := by decide
  rcases family_descends (prefixWord ++ tailWord_426573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426588 : List Nat := [2, 2, 4, 1, 3, 1, 2, 7]
def baseStart_426588 : Nat := 118140960795 + 426588 * 2 ^ 59
def prefixEnd_426588 : Nat := 4983230072969 + 3 ^ 40 * 426588 * 2
def baseEnd_426588 : Nat := 16225532254835718976901

theorem tailTrace_426588 : CollatzResearch.WordTrace tailWord_426588 prefixEnd_426588 16225532254835718976901 := by
  unfold tailWord_426588
  simp only [CollatzResearch.WordTrace]
  refine ⟨7779471289276003137596209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10372628385701337516794945 7779471289276003137596209)
  ·
    refine ⟨5834603466957002353197157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7779471289276003137596209 5834603466957002353197157)
    ·
      refine ⟨1093988150054437941224467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5834603466957002353197157 1093988150054437941224467)
      ·
        refine ⟨1640982225081656911836701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1093988150054437941224467 1640982225081656911836701)
        ·
          refine ⟨615368334405621341938763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1640982225081656911836701 615368334405621341938763)
          ·
            refine ⟨923052501608432012908145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615368334405621341938763 923052501608432012908145)
            ·
              refine ⟨692289376206324009681109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 923052501608432012908145 692289376206324009681109)
              ·
                refine ⟨16225532254835718976901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 692289376206324009681109 16225532254835718976901)
                ·
                  rfl

theorem cell22_426588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 7].length) (baseStart_426588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_426588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_426588 prefixEnd_426588 := by exact prefixLift 426588
  have htrace : WordTrace (prefixWord ++ tailWord_426588) baseStart_426588 baseEnd_426588 := by
    simpa [prefixWord, tailWord_426588, baseEnd_426588] using wordTrace_append hprefix tailTrace_426588
  have hstable : (prefixWord ++ tailWord_426588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426588).length < 2 ^ (prefixWord ++ tailWord_426588).sum := by decide
  have hdescent : baseEnd_426588 < baseStart_426588 := by decide
  rcases family_descends (prefixWord ++ tailWord_426588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426626 : List Nat := [3, 4, 3, 1, 1, 1, 2, 2, 2, 3]
def baseStart_426626 : Nat := 118140960795 + 426626 * 2 ^ 59
def prefixEnd_426626 : Nat := 4983230072969 + 3 ^ 40 * 426626 * 2
def baseEnd_426626 : Nat := 146042798470102038341993

theorem tailTrace_426626 : CollatzResearch.WordTrace tailWord_426626 prefixEnd_426626 146042798470102038341993 := by
  unfold tailWord_426626
  simp only [CollatzResearch.WordTrace]
  refine ⟨3890082138103584691268933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10373552368276225843383821 3890082138103584691268933)
  ·
    refine ⟨729390400894422129612925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3890082138103584691268933 729390400894422129612925)
    ·
      refine ⟨273521400335408298604847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 729390400894422129612925 273521400335408298604847)
      ·
        refine ⟨410282100503112447907271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273521400335408298604847 410282100503112447907271)
        ·
          refine ⟨615423150754668671860907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410282100503112447907271 615423150754668671860907)
          ·
            refine ⟨923134726132003007791361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615423150754668671860907 923134726132003007791361)
            ·
              refine ⟨692351044599002255843521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 923134726132003007791361 692351044599002255843521)
              ·
                refine ⟨519263283449251691882641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 692351044599002255843521 519263283449251691882641)
                ·
                  refine ⟨389447462586938768911981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 519263283449251691882641 389447462586938768911981)
                  ·
                    refine ⟨146042798470102038341993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 389447462586938768911981 146042798470102038341993)
                    ·
                      rfl

theorem cell22_426626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_426626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_426626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_426626 prefixEnd_426626 := by exact prefixLift 426626
  have htrace : WordTrace (prefixWord ++ tailWord_426626) baseStart_426626 baseEnd_426626 := by
    simpa [prefixWord, tailWord_426626, baseEnd_426626] using wordTrace_append hprefix tailTrace_426626
  have hstable : (prefixWord ++ tailWord_426626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426626).length < 2 ^ (prefixWord ++ tailWord_426626).sum := by decide
  have hdescent : baseEnd_426626 < baseStart_426626 := by decide
  rcases family_descends (prefixWord ++ tailWord_426626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426631 : List Nat := [1, 1, 4, 2, 1, 2, 2, 2, 2, 5]
def baseStart_426631 : Nat := 118140960795 + 426631 * 2 ^ 59
def prefixEnd_426631 : Nat := 4983230072969 + 3 ^ 40 * 426631 * 2
def baseEnd_426631 : Nat := 146044510072283691966977

theorem tailTrace_426631 : CollatzResearch.WordTrace tailWord_426631 prefixEnd_426631 146044510072283691966977 := by
  unfold tailWord_426631
  simp only [CollatzResearch.WordTrace]
  refine ⟨15560510917396224619007747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10373673944930816412671831 15560510917396224619007747)
  ·
    refine ⟨23340766376094336928511621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15560510917396224619007747 23340766376094336928511621)
    ·
      refine ⟨4376393695517688174095929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23340766376094336928511621 4376393695517688174095929)
      ·
        refine ⟨3282295271638266130571947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4376393695517688174095929 3282295271638266130571947)
        ·
          refine ⟨4923442907457399195857921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3282295271638266130571947 4923442907457399195857921)
          ·
            refine ⟨3692582180593049396893441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4923442907457399195857921 3692582180593049396893441)
            ·
              refine ⟨2769436635444787047670081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3692582180593049396893441 2769436635444787047670081)
              ·
                refine ⟨2077077476583590285752561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2769436635444787047670081 2077077476583590285752561)
                ·
                  refine ⟨1557808107437692714314421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2077077476583590285752561 1557808107437692714314421)
                  ·
                    refine ⟨146044510072283691966977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1557808107437692714314421 146044510072283691966977)
                    ·
                      rfl

theorem cell22_426631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_426631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_426631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_426631 prefixEnd_426631 := by exact prefixLift 426631
  have htrace : WordTrace (prefixWord ++ tailWord_426631) baseStart_426631 baseEnd_426631 := by
    simpa [prefixWord, tailWord_426631, baseEnd_426631] using wordTrace_append hprefix tailTrace_426631
  have hstable : (prefixWord ++ tailWord_426631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426631).length < 2 ^ (prefixWord ++ tailWord_426631).sum := by decide
  have hdescent : baseEnd_426631 < baseStart_426631 := by decide
  rcases family_descends (prefixWord ++ tailWord_426631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426723 : List Nat := [1, 1, 1, 7, 1, 2, 1, 8]
def baseStart_426723 : Nat := 118140960795 + 426723 * 2 ^ 59
def prefixEnd_426723 : Nat := 4983230072969 + 3 ^ 40 * 426723 * 2
def baseEnd_426723 : Nat := 16230667061380679851855

theorem tailTrace_426723 : CollatzResearch.WordTrace tailWord_426723 prefixEnd_426723 16230667061380679851855 := by
  unfold tailWord_426723
  simp only [CollatzResearch.WordTrace]
  refine ⟨15563866433062924331356823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10375910955375282887571215 15563866433062924331356823)
  ·
    refine ⟨23345799649594386497035235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15563866433062924331356823 23345799649594386497035235)
    ·
      refine ⟨35018699474391579745552853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23345799649594386497035235 35018699474391579745552853)
      ·
        refine ⟨820750768931052650286395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 35018699474391579745552853 820750768931052650286395)
        ·
          refine ⟨1231126153396578975429593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 820750768931052650286395 1231126153396578975429593)
          ·
            refine ⟨923344615047434231572195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1231126153396578975429593 923344615047434231572195)
            ·
              refine ⟨1385016922571151347358293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 923344615047434231572195 1385016922571151347358293)
              ·
                refine ⟨16230667061380679851855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1385016922571151347358293 16230667061380679851855)
                ·
                  rfl

theorem cell22_426723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 8].length) (baseStart_426723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_426723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_426723 prefixEnd_426723 := by exact prefixLift 426723
  have htrace : WordTrace (prefixWord ++ tailWord_426723) baseStart_426723 baseEnd_426723 := by
    simpa [prefixWord, tailWord_426723, baseEnd_426723] using wordTrace_append hprefix tailTrace_426723
  have hstable : (prefixWord ++ tailWord_426723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426723).length < 2 ^ (prefixWord ++ tailWord_426723).sum := by decide
  have hdescent : baseEnd_426723 < baseStart_426723 := by decide
  rcases family_descends (prefixWord ++ tailWord_426723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426806 : List Nat := [5, 1, 2, 2, 2, 1, 1, 4, 1, 3]
def baseStart_426806 : Nat := 118140960795 + 426806 * 2 ^ 59
def prefixEnd_426806 : Nat := 4983230072969 + 3 ^ 40 * 426806 * 2
def baseEnd_426806 : Nat := 146104416148641568841441

theorem tailTrace_426806 : CollatzResearch.WordTrace tailWord_426806 prefixEnd_426806 146104416148641568841441 := by
  unfold tailWord_426806
  simp only [CollatzResearch.WordTrace]
  refine ⟨972930855735139344164267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10377929127841486337752181 972930855735139344164267)
  ·
    refine ⟨1459396283602709016246401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 972930855735139344164267 1459396283602709016246401)
    ·
      refine ⟨1094547212702031762184801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1459396283602709016246401 1094547212702031762184801)
      ·
        refine ⟨820910409526523821638601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1094547212702031762184801 820910409526523821638601)
        ·
          refine ⟨615682807144892866228951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 820910409526523821638601 615682807144892866228951)
          ·
            refine ⟨923524210717339299343427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615682807144892866228951 923524210717339299343427)
            ·
              refine ⟨1385286316076008949015141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 923524210717339299343427 1385286316076008949015141)
              ·
                refine ⟨259741184264251677940339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1385286316076008949015141 259741184264251677940339)
                ·
                  refine ⟨389611776396377516910509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 259741184264251677940339 389611776396377516910509)
                  ·
                    refine ⟨146104416148641568841441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 389611776396377516910509 146104416148641568841441)
                    ·
                      rfl

theorem cell22_426806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_426806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_426806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_426806 prefixEnd_426806 := by exact prefixLift 426806
  have htrace : WordTrace (prefixWord ++ tailWord_426806) baseStart_426806 baseEnd_426806 := by
    simpa [prefixWord, tailWord_426806, baseEnd_426806] using wordTrace_append hprefix tailTrace_426806
  have hstable : (prefixWord ++ tailWord_426806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426806).length < 2 ^ (prefixWord ++ tailWord_426806).sum := by decide
  have hdescent : baseEnd_426806 < baseStart_426806 := by decide
  rcases family_descends (prefixWord ++ tailWord_426806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426817 : List Nat := [1, 2, 5, 3, 1, 1, 1, 1, 2, 5]
def baseStart_426817 : Nat := 118140960795 + 426817 * 2 ^ 59
def prefixEnd_426817 : Nat := 4983230072969 + 3 ^ 40 * 426817 * 2
def baseEnd_426817 : Nat := 146108181673441206816407

theorem tailTrace_426817 : CollatzResearch.WordTrace tailWord_426817 prefixEnd_426817 146108181673441206816407 := by
  unfold tailWord_426817
  simp only [CollatzResearch.WordTrace]
  refine ⟨15567294894722378385278705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10378196596481585590185803 15567294894722378385278705)
  ·
    refine ⟨11675471171041783788959029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15567294894722378385278705 11675471171041783788959029)
    ·
      refine ⟨1094575422285167230214909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11675471171041783788959029 1094575422285167230214909)
      ·
        refine ⟨410465783356937711330591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1094575422285167230214909 410465783356937711330591)
        ·
          refine ⟨615698675035406566995887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410465783356937711330591 615698675035406566995887)
          ·
            refine ⟨923548012553109850493831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615698675035406566995887 923548012553109850493831)
            ·
              refine ⟨1385322018829664775740747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 923548012553109850493831 1385322018829664775740747)
              ·
                refine ⟨2077983028244497163611121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1385322018829664775740747 2077983028244497163611121)
                ·
                  refine ⟨1558487271183372872708341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2077983028244497163611121 1558487271183372872708341)
                  ·
                    refine ⟨146108181673441206816407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1558487271183372872708341 146108181673441206816407)
                    ·
                      rfl

theorem cell22_426817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_426817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_426817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_426817 prefixEnd_426817 := by exact prefixLift 426817
  have htrace : WordTrace (prefixWord ++ tailWord_426817) baseStart_426817 baseEnd_426817 := by
    simpa [prefixWord, tailWord_426817, baseEnd_426817] using wordTrace_append hprefix tailTrace_426817
  have hstable : (prefixWord ++ tailWord_426817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426817).length < 2 ^ (prefixWord ++ tailWord_426817).sum := by decide
  have hdescent : baseEnd_426817 < baseStart_426817 := by decide
  rcases family_descends (prefixWord ++ tailWord_426817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426903 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 9]
def baseStart_426903 : Nat := 118140960795 + 426903 * 2 ^ 59
def prefixEnd_426903 : Nat := 4983230072969 + 3 ^ 40 * 426903 * 2
def baseEnd_426903 : Nat := 48712540410321883055381

theorem tailTrace_426903 : CollatzResearch.WordTrace tailWord_426903 prefixEnd_426903 48712540410321883055381 := by
  unfold tailWord_426903
  simp only [CollatzResearch.WordTrace]
  refine ⟨15570431572410815072909363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10380287714940543381939575 15570431572410815072909363)
  ·
    refine ⟨23355647358616222609364045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15570431572410815072909363 23355647358616222609364045)
    ·
      refine ⟨8758367759481083478511517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23355647358616222609364045 8758367759481083478511517)
      ·
        refine ⟨3284387909805406304441819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8758367759481083478511517 3284387909805406304441819)
        ·
          refine ⟨4926581864708109456662729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3284387909805406304441819 4926581864708109456662729)
          ·
            refine ⟨3694936398531082092497047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4926581864708109456662729 3694936398531082092497047)
            ·
              refine ⟨5542404597796623138745571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3694936398531082092497047 5542404597796623138745571)
              ·
                refine ⟨8313606896694934708118357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5542404597796623138745571 8313606896694934708118357)
                ·
                  refine ⟨48712540410321883055381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 8313606896694934708118357 48712540410321883055381)
                  ·
                    rfl

theorem cell22_426903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 9].length) (baseStart_426903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_426903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_426903 prefixEnd_426903 := by exact prefixLift 426903
  have htrace : WordTrace (prefixWord ++ tailWord_426903) baseStart_426903 baseEnd_426903 := by
    simpa [prefixWord, tailWord_426903, baseEnd_426903] using wordTrace_append hprefix tailTrace_426903
  have hstable : (prefixWord ++ tailWord_426903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426903).length < 2 ^ (prefixWord ++ tailWord_426903).sum := by decide
  have hdescent : baseEnd_426903 < baseStart_426903 := by decide
  rcases family_descends (prefixWord ++ tailWord_426903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_426937 : List Nat := [1, 2, 1, 4, 2, 2, 4, 1, 5]
def baseStart_426937 : Nat := 118140960795 + 426937 * 2 ^ 59
def prefixEnd_426937 : Nat := 4983230072969 + 3 ^ 40 * 426937 * 2
def baseEnd_426937 : Nat := 48716420041933631272013

theorem tailTrace_426937 : CollatzResearch.WordTrace tailWord_426937 prefixEnd_426937 48716420041933631272013 := by
  unfold tailWord_426937
  simp only [CollatzResearch.WordTrace]
  refine ⟨15571671654287638879647065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10381114436191759253098043 15571671654287638879647065)
  ·
    refine ⟨11678753740715729159735299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15571671654287638879647065 11678753740715729159735299)
    ·
      refine ⟨17518130611073593739602949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11678753740715729159735299 17518130611073593739602949)
      ·
        refine ⟨3284649489576298826175553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17518130611073593739602949 3284649489576298826175553)
        ·
          refine ⟨2463487117182224119631665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3284649489576298826175553 2463487117182224119631665)
          ·
            refine ⟨1847615337886668089723749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2463487117182224119631665 1847615337886668089723749)
            ·
              refine ⟨346427875853750266823203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1847615337886668089723749 346427875853750266823203)
              ·
                refine ⟨519641813780625400234805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 346427875853750266823203 519641813780625400234805)
                ·
                  refine ⟨48716420041933631272013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 519641813780625400234805 48716420041933631272013)
                  ·
                    rfl

theorem cell22_426937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 5].length) (baseStart_426937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_426937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_426937 prefixEnd_426937 := by exact prefixLift 426937
  have htrace : WordTrace (prefixWord ++ tailWord_426937) baseStart_426937 baseEnd_426937 := by
    simpa [prefixWord, tailWord_426937, baseEnd_426937] using wordTrace_append hprefix tailTrace_426937
  have hstable : (prefixWord ++ tailWord_426937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_426937).length < 2 ^ (prefixWord ++ tailWord_426937).sum := by decide
  have hdescent : baseEnd_426937 < baseStart_426937 := by decide
  rcases family_descends (prefixWord ++ tailWord_426937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427031 : List Nat := [1, 1, 3, 5, 1, 3, 1, 2, 2, 3]
def baseStart_427031 : Nat := 118140960795 + 427031 * 2 ^ 59
def prefixEnd_427031 : Nat := 4983230072969 + 3 ^ 40 * 427031 * 2
def baseEnd_427031 : Nat := 146181438246815981965751

theorem tailTrace_427031 : CollatzResearch.WordTrace tailWord_427031 prefixEnd_427031 146181438246815981965751 := by
  unfold tailWord_427031
  simp only [CollatzResearch.WordTrace]
  refine ⟨15575100115947092933568947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10383400077298061955712631 15575100115947092933568947)
  ·
    refine ⟨23362650173920639400353421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15575100115947092933568947 23362650173920639400353421)
    ·
      refine ⟨8760993815220239775132533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23362650173920639400353421 8760993815220239775132533)
      ·
        refine ⟨821343170176897478918675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8760993815220239775132533 821343170176897478918675)
        ·
          refine ⟨1232014755265346218378013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 821343170176897478918675 1232014755265346218378013)
          ·
            refine ⟨462005533224504831891755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1232014755265346218378013 462005533224504831891755)
            ·
              refine ⟨693008299836757247837633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462005533224504831891755 693008299836757247837633)
              ·
                refine ⟨519756224877567935878225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 693008299836757247837633 519756224877567935878225)
                ·
                  refine ⟨389817168658175951908669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 519756224877567935878225 389817168658175951908669)
                  ·
                    refine ⟨146181438246815981965751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 389817168658175951908669 146181438246815981965751)
                    ·
                      rfl

theorem cell22_427031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 2, 3].length) (baseStart_427031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_427031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_427031 prefixEnd_427031 := by exact prefixLift 427031
  have htrace : WordTrace (prefixWord ++ tailWord_427031) baseStart_427031 baseEnd_427031 := by
    simpa [prefixWord, tailWord_427031, baseEnd_427031] using wordTrace_append hprefix tailTrace_427031
  have hstable : (prefixWord ++ tailWord_427031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427031).length < 2 ^ (prefixWord ++ tailWord_427031).sum := by decide
  have hdescent : baseEnd_427031 < baseStart_427031 := by decide
  rcases family_descends (prefixWord ++ tailWord_427031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427106 : List Nat := [3, 3, 2, 2, 1, 1, 4, 1, 5]
def baseStart_427106 : Nat := 118140960795 + 427106 * 2 ^ 59
def prefixEnd_427106 : Nat := 4983230072969 + 3 ^ 40 * 427106 * 2
def baseEnd_427106 : Nat := 48735704093180262113507

theorem tailTrace_427106 : CollatzResearch.WordTrace tailWord_427106 prefixEnd_427106 48735704093180262113507 := by
  unfold tailWord_427106
  simp only [CollatzResearch.WordTrace]
  refine ⟨3894458897668845185637293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10385223727116920495032781 3894458897668845185637293)
  ·
    refine ⟨1460422086625816944613985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3894458897668845185637293 1460422086625816944613985)
    ·
      refine ⟨1095316564969362708460489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1460422086625816944613985 1095316564969362708460489)
      ·
        refine ⟨821487423727022031345367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1095316564969362708460489 821487423727022031345367)
        ·
          refine ⟨1232231135590533047018051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 821487423727022031345367 1232231135590533047018051)
          ·
            refine ⟨1848346703385799570527077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1232231135590533047018051 1848346703385799570527077)
            ·
              refine ⟨346565006884837419473827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1848346703385799570527077 346565006884837419473827)
              ·
                refine ⟨519847510327256129210741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 346565006884837419473827 519847510327256129210741)
                ·
                  refine ⟨48735704093180262113507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 519847510327256129210741 48735704093180262113507)
                  ·
                    rfl

theorem cell22_427106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_427106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_427106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_427106 prefixEnd_427106 := by exact prefixLift 427106
  have htrace : WordTrace (prefixWord ++ tailWord_427106) baseStart_427106 baseEnd_427106 := by
    simpa [prefixWord, tailWord_427106, baseEnd_427106] using wordTrace_append hprefix tailTrace_427106
  have hstable : (prefixWord ++ tailWord_427106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427106).length < 2 ^ (prefixWord ++ tailWord_427106).sum := by decide
  have hdescent : baseEnd_427106 < baseStart_427106 := by decide
  rcases family_descends (prefixWord ++ tailWord_427106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427115 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 7, 5]
def baseStart_427115 : Nat := 118140960795 + 427115 * 2 ^ 59
def prefixEnd_427115 : Nat := 4983230072969 + 3 ^ 40 * 427115 * 2
def baseEnd_427115 : Nat := 146210193163467762865493

theorem tailTrace_427115 : CollatzResearch.WordTrace tailWord_427115 prefixEnd_427115 146210193163467762865493 := by
  unfold tailWord_427115
  simp only [CollatzResearch.WordTrace]
  refine ⟨15578163847642775279626799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10385442565095183519751199 15578163847642775279626799)
  ·
    refine ⟨23367245771464162919440199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15578163847642775279626799 23367245771464162919440199)
    ·
      refine ⟨35050868657196244379160299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23367245771464162919440199 35050868657196244379160299)
      ·
        refine ⟨52576302985794366568740449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35050868657196244379160299 52576302985794366568740449)
        ·
          refine ⟨39432227239345774926555337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52576302985794366568740449 39432227239345774926555337)
          ·
            refine ⟨29574170429509331194916503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39432227239345774926555337 29574170429509331194916503)
            ·
              refine ⟨44361255644263996792374755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29574170429509331194916503 44361255644263996792374755)
              ·
                refine ⟨66541883466395995188562133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44361255644263996792374755 66541883466395995188562133)
                ·
                  refine ⟨1559575393743656137231925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 66541883466395995188562133 1559575393743656137231925)
                  ·
                    refine ⟨146210193163467762865493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1559575393743656137231925 146210193163467762865493)
                    ·
                      rfl

theorem cell22_427115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 5].length) (baseStart_427115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_427115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_427115 prefixEnd_427115 := by exact prefixLift 427115
  have htrace : WordTrace (prefixWord ++ tailWord_427115) baseStart_427115 baseEnd_427115 := by
    simpa [prefixWord, tailWord_427115, baseEnd_427115] using wordTrace_append hprefix tailTrace_427115
  have hstable : (prefixWord ++ tailWord_427115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427115).length < 2 ^ (prefixWord ++ tailWord_427115).sum := by decide
  have hdescent : baseEnd_427115 < baseStart_427115 := by decide
  rcases family_descends (prefixWord ++ tailWord_427115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427132 : List Nat := [2, 2, 2, 1, 1, 3, 3, 2, 1, 5]
def baseStart_427132 : Nat := 118140960795 + 427132 * 2 ^ 59
def prefixEnd_427132 : Nat := 4983230072969 + 3 ^ 40 * 427132 * 2
def baseEnd_427132 : Nat := 146216012610885385190441

theorem tailTrace_427132 : CollatzResearch.WordTrace tailWord_427132 prefixEnd_427132 146216012610885385190441 := by
  unfold tailWord_427132
  simp only [CollatzResearch.WordTrace]
  refine ⟨7789391944290593591497825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10385855925720791455330433 7789391944290593591497825)
  ·
    refine ⟨5842043958217945193623369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7789391944290593591497825 5842043958217945193623369)
    ·
      refine ⟨4381532968663458895217527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5842043958217945193623369 4381532968663458895217527)
      ·
        refine ⟨6572299452995188342826291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4381532968663458895217527 6572299452995188342826291)
        ·
          refine ⟨9858449179492782514239437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6572299452995188342826291 9858449179492782514239437)
          ·
            refine ⟨3696918442309793442839789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9858449179492782514239437 3696918442309793442839789)
            ·
              refine ⟨1386344415866172541064921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3696918442309793442839789 1386344415866172541064921)
              ·
                refine ⟨1039758311899629405798691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1386344415866172541064921 1039758311899629405798691)
                ·
                  refine ⟨1559637467849444108698037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1039758311899629405798691 1559637467849444108698037)
                  ·
                    refine ⟨146216012610885385190441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1559637467849444108698037 146216012610885385190441)
                    ·
                      rfl

theorem cell22_427132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_427132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_427132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_427132 prefixEnd_427132 := by exact prefixLift 427132
  have htrace : WordTrace (prefixWord ++ tailWord_427132) baseStart_427132 baseEnd_427132 := by
    simpa [prefixWord, tailWord_427132, baseEnd_427132] using wordTrace_append hprefix tailTrace_427132
  have hstable : (prefixWord ++ tailWord_427132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427132).length < 2 ^ (prefixWord ++ tailWord_427132).sum := by decide
  have hdescent : baseEnd_427132 < baseStart_427132 := by decide
  rcases family_descends (prefixWord ++ tailWord_427132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427145 : List Nat := [1, 2, 1, 1, 4, 13]
def baseStart_427145 : Nat := 118140960795 + 427145 * 2 ^ 59
def prefixEnd_427145 : Nat := 4983230072969 + 3 ^ 40 * 427145 * 2
def baseEnd_427145 : Nat := 1805190898476020797721

theorem tailTrace_427145 : CollatzResearch.WordTrace tailWord_427145 prefixEnd_427145 1805190898476020797721 := by
  unfold tailWord_427145
  simp only [CollatzResearch.WordTrace]
  refine ⟨15579258037534090403218889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10386172025022726935479259 15579258037534090403218889)
  ·
    refine ⟨11684443528150567802414167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15579258037534090403218889 11684443528150567802414167)
    ·
      refine ⟨17526665292225851703621251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11684443528150567802414167 17526665292225851703621251)
      ·
        refine ⟨26289997938338777555431877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17526665292225851703621251 26289997938338777555431877)
        ·
          refine ⟨4929374613438520791643477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26289997938338777555431877 4929374613438520791643477)
          ·
            refine ⟨1805190898476020797721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 4929374613438520791643477 1805190898476020797721)
            ·
              rfl

theorem cell22_427145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 13].length) (baseStart_427145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_427145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_427145 prefixEnd_427145 := by exact prefixLift 427145
  have htrace : WordTrace (prefixWord ++ tailWord_427145) baseStart_427145 baseEnd_427145 := by
    simpa [prefixWord, tailWord_427145, baseEnd_427145] using wordTrace_append hprefix tailTrace_427145
  have hstable : (prefixWord ++ tailWord_427145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427145).length < 2 ^ (prefixWord ++ tailWord_427145).sum := by decide
  have hdescent : baseEnd_427145 < baseStart_427145 := by decide
  rcases family_descends (prefixWord ++ tailWord_427145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427166 : List Nat := [4, 3, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_427166 : Nat := 118140960795 + 427166 * 2 ^ 59
def prefixEnd_427166 : Nat := 4983230072969 + 3 ^ 40 * 427166 * 2
def baseEnd_427166 : Nat := 146227651505720629840337

theorem tailTrace_427166 : CollatzResearch.WordTrace tailWord_427166 prefixEnd_427166 146227651505720629840337 := by
  unfold tailWord_427166
  simp only [CollatzResearch.WordTrace]
  refine ⟨1947502996307251373716669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10386682646972007326488901 1947502996307251373716669)
  ·
    refine ⟨730313623615219265143751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1947502996307251373716669 730313623615219265143751)
    ·
      refine ⟨1095470435422828897715627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 730313623615219265143751 1095470435422828897715627)
      ·
        refine ⟨1643205653134243346573441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1095470435422828897715627 1643205653134243346573441)
        ·
          refine ⟨1232404239850682509930081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1643205653134243346573441 1232404239850682509930081)
          ·
            refine ⟨924303179888011882447561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1232404239850682509930081 924303179888011882447561)
            ·
              refine ⟨693227384916008911835671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 924303179888011882447561 693227384916008911835671)
              ·
                refine ⟨1039841077374013367753507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 693227384916008911835671 1039841077374013367753507)
                ·
                  refine ⟨1559761616061020051630261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1039841077374013367753507 1559761616061020051630261)
                  ·
                    refine ⟨146227651505720629840337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1559761616061020051630261 146227651505720629840337)
                    ·
                      rfl

theorem cell22_427166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_427166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_427166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_427166 prefixEnd_427166 := by exact prefixLift 427166
  have htrace : WordTrace (prefixWord ++ tailWord_427166) baseStart_427166 baseEnd_427166 := by
    simpa [prefixWord, tailWord_427166, baseEnd_427166] using wordTrace_append hprefix tailTrace_427166
  have hstable : (prefixWord ++ tailWord_427166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427166).length < 2 ^ (prefixWord ++ tailWord_427166).sum := by decide
  have hdescent : baseEnd_427166 < baseStart_427166 := by decide
  rcases family_descends (prefixWord ++ tailWord_427166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427245 : List Nat := [1, 5, 1, 2, 2, 3, 1, 3, 1, 3]
def baseStart_427245 : Nat := 118140960795 + 427245 * 2 ^ 59
def prefixEnd_427245 : Nat := 4983230072969 + 3 ^ 40 * 427245 * 2
def baseEnd_427245 : Nat := 146254694820190757115095

theorem tailTrace_427245 : CollatzResearch.WordTrace tailWord_427245 prefixEnd_427245 146254694820190757115095 := by
  unfold tailWord_427245
  simp only [CollatzResearch.WordTrace]
  refine ⟨15582905337171807481859189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10388603558114538321239459 15582905337171807481859189)
  ·
    refine ⟨1460897375359856951424299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15582905337171807481859189 1460897375359856951424299)
    ·
      refine ⟨2191346063039785427136449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1460897375359856951424299 2191346063039785427136449)
      ·
        refine ⟨1643509547279839070352337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2191346063039785427136449 1643509547279839070352337)
        ·
          refine ⟨1232632160459879302764253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1643509547279839070352337 1232632160459879302764253)
          ·
            refine ⟨462237060172454738536595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1232632160459879302764253 462237060172454738536595)
            ·
              refine ⟨693355590258682107804893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462237060172454738536595 693355590258682107804893)
              ·
                refine ⟨260008346347005790426835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 693355590258682107804893 260008346347005790426835)
                ·
                  refine ⟨390012519520508685640253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 260008346347005790426835 390012519520508685640253)
                  ·
                    refine ⟨146254694820190757115095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 390012519520508685640253 146254694820190757115095)
                    ·
                      rfl

theorem cell22_427245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_427245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_427245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_427245 prefixEnd_427245 := by exact prefixLift 427245
  have htrace : WordTrace (prefixWord ++ tailWord_427245) baseStart_427245 baseEnd_427245 := by
    simpa [prefixWord, tailWord_427245, baseEnd_427245] using wordTrace_append hprefix tailTrace_427245
  have hstable : (prefixWord ++ tailWord_427245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427245).length < 2 ^ (prefixWord ++ tailWord_427245).sum := by decide
  have hdescent : baseEnd_427245 < baseStart_427245 := by decide
  rcases family_descends (prefixWord ++ tailWord_427245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427254 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 5, 4]
def baseStart_427254 : Nat := 118140960795 + 427254 * 2 ^ 59
def prefixEnd_427254 : Nat := 4983230072969 + 3 ^ 40 * 427254 * 2
def baseEnd_427254 : Nat := 146257775704117733640067

theorem tailTrace_427254 : CollatzResearch.WordTrace tailWord_427254 prefixEnd_427254 146257775704117733640067 := by
  unfold tailWord_427254
  simp only [CollatzResearch.WordTrace]
  refine ⟨973952099633700126183551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10388822396092801345957877 973952099633700126183551)
  ·
    refine ⟨1460928149450550189275327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 973952099633700126183551 1460928149450550189275327)
    ·
      refine ⟨2191392224175825283912991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1460928149450550189275327 2191392224175825283912991)
      ·
        refine ⟨3287088336263737925869487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2191392224175825283912991 3287088336263737925869487)
        ·
          refine ⟨4930632504395606888804231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3287088336263737925869487 4930632504395606888804231)
          ·
            refine ⟨7395948756593410333206347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4930632504395606888804231 7395948756593410333206347)
            ·
              refine ⟨11093923134890115499809521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7395948756593410333206347 11093923134890115499809521)
              ·
                refine ⟨8320442351167586624857141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11093923134890115499809521 8320442351167586624857141)
                ·
                  refine ⟨780041470421961246080357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8320442351167586624857141 780041470421961246080357)
                  ·
                    refine ⟨146257775704117733640067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 780041470421961246080357 146257775704117733640067)
                    ·
                      rfl

theorem cell22_427254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_427254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_427254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_427254 prefixEnd_427254 := by exact prefixLift 427254
  have htrace : WordTrace (prefixWord ++ tailWord_427254) baseStart_427254 baseEnd_427254 := by
    simpa [prefixWord, tailWord_427254, baseEnd_427254] using wordTrace_append hprefix tailTrace_427254
  have hstable : (prefixWord ++ tailWord_427254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427254).length < 2 ^ (prefixWord ++ tailWord_427254).sum := by decide
  have hdescent : baseEnd_427254 < baseStart_427254 := by decide
  rcases family_descends (prefixWord ++ tailWord_427254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427299 : List Nat := [1, 1, 1, 4, 2, 3, 1, 3, 2, 4]
def baseStart_427299 : Nat := 118140960795 + 427299 * 2 ^ 59
def prefixEnd_427299 : Nat := 4983230072969 + 3 ^ 40 * 427299 * 2
def baseEnd_427299 : Nat := 146273180123752616264929

theorem tailTrace_427299 : CollatzResearch.WordTrace tailWord_427299 prefixEnd_427299 146273180123752616264929 := by
  unfold tailWord_427299
  simp only [CollatzResearch.WordTrace]
  refine ⟨15584874878976174704324951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10389916585984116469549967 15584874878976174704324951)
  ·
    refine ⟨23377312318464262056487427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15584874878976174704324951 23377312318464262056487427)
    ·
      refine ⟨35065968477696393084731141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23377312318464262056487427 35065968477696393084731141)
      ·
        refine ⟨6574869089568073703387089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35065968477696393084731141 6574869089568073703387089)
        ·
          refine ⟨4931151817176055277540317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6574869089568073703387089 4931151817176055277540317)
          ·
            refine ⟨1849181931441020729077619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4931151817176055277540317 1849181931441020729077619)
            ·
              refine ⟨2773772897161531093616429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1849181931441020729077619 2773772897161531093616429)
              ·
                refine ⟨1040164836435574160106161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2773772897161531093616429 1040164836435574160106161)
                ·
                  refine ⟨780123627326680620079621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1040164836435574160106161 780123627326680620079621)
                  ·
                    refine ⟨146273180123752616264929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 780123627326680620079621 146273180123752616264929)
                    ·
                      rfl

theorem cell22_427299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 4].length) (baseStart_427299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_427299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_427299 prefixEnd_427299 := by exact prefixLift 427299
  have htrace : WordTrace (prefixWord ++ tailWord_427299) baseStart_427299 baseEnd_427299 := by
    simpa [prefixWord, tailWord_427299, baseEnd_427299] using wordTrace_append hprefix tailTrace_427299
  have hstable : (prefixWord ++ tailWord_427299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427299).length < 2 ^ (prefixWord ++ tailWord_427299).sum := by decide
  have hdescent : baseEnd_427299 < baseStart_427299 := by decide
  rcases family_descends (prefixWord ++ tailWord_427299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427316 : List Nat := [2, 5, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_427316 : Nat := 118140960795 + 427316 * 2 ^ 59
def prefixEnd_427316 : Nat := 4983230072969 + 3 ^ 40 * 427316 * 2
def baseEnd_427316 : Nat := 146278999571170238589877

theorem tailTrace_427316 : CollatzResearch.WordTrace tailWord_427316 prefixEnd_427316 146278999571170238589877 := by
  unfold tailWord_427316
  simp only [CollatzResearch.WordTrace]
  refine ⟨7792747459957293303846901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10390329946609724405129201 7792747459957293303846901)
  ·
    refine ⟨730570074370996247235647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7792747459957293303846901 730570074370996247235647)
    ·
      refine ⟨1095855111556494370853471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 730570074370996247235647 1095855111556494370853471)
      ·
        refine ⟨1643782667334741556280207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1095855111556494370853471 1643782667334741556280207)
        ·
          refine ⟨2465674001002112334420311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1643782667334741556280207 2465674001002112334420311)
          ·
            refine ⟨3698511001503168501630467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2465674001002112334420311 3698511001503168501630467)
            ·
              refine ⟨5547766502254752752445701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3698511001503168501630467 5547766502254752752445701)
              ·
                refine ⟨1040206219172766141083569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5547766502254752752445701 1040206219172766141083569)
                ·
                  refine ⟨780154664379574605812677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1040206219172766141083569 780154664379574605812677)
                  ·
                    refine ⟨146278999571170238589877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 780154664379574605812677 146278999571170238589877)
                    ·
                      rfl

theorem cell22_427316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_427316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_427316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_427316 prefixEnd_427316 := by exact prefixLift 427316
  have htrace : WordTrace (prefixWord ++ tailWord_427316) baseStart_427316 baseEnd_427316 := by
    simpa [prefixWord, tailWord_427316, baseEnd_427316] using wordTrace_append hprefix tailTrace_427316
  have hstable : (prefixWord ++ tailWord_427316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427316).length < 2 ^ (prefixWord ++ tailWord_427316).sum := by decide
  have hdescent : baseEnd_427316 < baseStart_427316 := by decide
  rcases family_descends (prefixWord ++ tailWord_427316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427363 : List Nat := [1, 1, 1, 5, 2, 2, 1, 5, 1, 3]
def baseStart_427363 : Nat := 118140960795 + 427363 * 2 ^ 59
def prefixEnd_427363 : Nat := 4983230072969 + 3 ^ 40 * 427363 * 2
def baseEnd_427363 : Nat := 146295088631677782664733

theorem tailTrace_427363 : CollatzResearch.WordTrace tailWord_427363 prefixEnd_427363 146295088631677782664733 := by
  unfold tailWord_427363
  simp only [CollatzResearch.WordTrace]
  refine ⟨15587209150744313634654743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10391472767162875756436495 15587209150744313634654743)
  ·
    refine ⟨23380813726116470451982115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15587209150744313634654743 23380813726116470451982115)
    ·
      refine ⟨35071220589174705677973173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23380813726116470451982115 35071220589174705677973173)
      ·
        refine ⟨3287926930235128657309985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35071220589174705677973173 3287926930235128657309985)
        ·
          refine ⟨2465945197676346492982489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3287926930235128657309985 2465945197676346492982489)
          ·
            refine ⟨1849458898257259869736867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2465945197676346492982489 1849458898257259869736867)
            ·
              refine ⟨2774188347385889804605301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1849458898257259869736867 2774188347385889804605301)
              ·
                refine ⟨260080157567427169181747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2774188347385889804605301 260080157567427169181747)
                ·
                  refine ⟨390120236351140753772621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 260080157567427169181747 390120236351140753772621)
                  ·
                    refine ⟨146295088631677782664733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 390120236351140753772621 146295088631677782664733)
                    ·
                      rfl

theorem cell22_427363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 5, 1, 3].length) (baseStart_427363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_427363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_427363 prefixEnd_427363 := by exact prefixLift 427363
  have htrace : WordTrace (prefixWord ++ tailWord_427363) baseStart_427363 baseEnd_427363 := by
    simpa [prefixWord, tailWord_427363, baseEnd_427363] using wordTrace_append hprefix tailTrace_427363
  have hstable : (prefixWord ++ tailWord_427363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427363).length < 2 ^ (prefixWord ++ tailWord_427363).sum := by decide
  have hdescent : baseEnd_427363 < baseStart_427363 := by decide
  rcases family_descends (prefixWord ++ tailWord_427363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427404 : List Nat := [2, 2, 1, 2, 1, 3, 1, 4, 6]
def baseStart_427404 : Nat := 118140960795 + 427404 * 2 ^ 59
def prefixEnd_427404 : Nat := 4983230072969 + 3 ^ 40 * 427404 * 2
def baseEnd_427404 : Nat := 48769707923189114129869

theorem tailTrace_427404 : CollatzResearch.WordTrace tailWord_427404 prefixEnd_427404 48769707923189114129869 := by
  unfold tailWord_427404
  simp only [CollatzResearch.WordTrace]
  refine ⟨7794352271797888818448633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10392469695730518424598177 7794352271797888818448633)
  ·
    refine ⟨5845764203848416613836475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7794352271797888818448633 5845764203848416613836475)
    ·
      refine ⟨8768646305772624920754713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5845764203848416613836475 8768646305772624920754713)
      ·
        refine ⟨6576484729329468690566035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8768646305772624920754713 6576484729329468690566035)
        ·
          refine ⟨9864727093994203035849053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6576484729329468690566035 9864727093994203035849053)
          ·
            refine ⟨3699272660247826138443395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9864727093994203035849053 3699272660247826138443395)
            ·
              refine ⟨5548908990371739207665093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3699272660247826138443395 5548908990371739207665093)
              ·
                refine ⟨1040420435694701101437205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5548908990371739207665093 1040420435694701101437205)
                ·
                  refine ⟨48769707923189114129869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1040420435694701101437205 48769707923189114129869)
                  ·
                    rfl

theorem cell22_427404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 6].length) (baseStart_427404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_427404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_427404 prefixEnd_427404 := by exact prefixLift 427404
  have htrace : WordTrace (prefixWord ++ tailWord_427404) baseStart_427404 baseEnd_427404 := by
    simpa [prefixWord, tailWord_427404, baseEnd_427404] using wordTrace_append hprefix tailTrace_427404
  have hstable : (prefixWord ++ tailWord_427404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427404).length < 2 ^ (prefixWord ++ tailWord_427404).sum := by decide
  have hdescent : baseEnd_427404 < baseStart_427404 := by decide
  rcases family_descends (prefixWord ++ tailWord_427404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427436 : List Nat := [2, 2, 1, 1, 1, 1, 6, 1, 4, 3]
def baseStart_427436 : Nat := 118140960795 + 427436 * 2 ^ 59
def prefixEnd_427436 : Nat := 4983230072969 + 3 ^ 40 * 427436 * 2
def baseEnd_427436 : Nat := 146320078023529925589509

theorem tailTrace_427436 : CollatzResearch.WordTrace tailWord_427436 prefixEnd_427436 146320078023529925589509 := by
  unfold tailWord_427436
  simp only [CollatzResearch.WordTrace]
  refine ⟨7794935839739923551031081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10393247786319898068041441 7794935839739923551031081)
  ·
    refine ⟨5846201879804942663273311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7794935839739923551031081 5846201879804942663273311)
    ·
      refine ⟨8769302819707413994909967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5846201879804942663273311 8769302819707413994909967)
      ·
        refine ⟨13153954229561120992364951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8769302819707413994909967 13153954229561120992364951)
        ·
          refine ⟨19730931344341681488547427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13153954229561120992364951 19730931344341681488547427)
          ·
            refine ⟨29596397016512522232821141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19730931344341681488547427 29596397016512522232821141)
            ·
              refine ⟨1387331110149024479663491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29596397016512522232821141 1387331110149024479663491)
              ·
                refine ⟨2080996665223536719495237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1387331110149024479663491 2080996665223536719495237)
                ·
                  refine ⟨390186874729413134905357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2080996665223536719495237 390186874729413134905357)
                  ·
                    refine ⟨146320078023529925589509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 390186874729413134905357 146320078023529925589509)
                    ·
                      rfl

theorem cell22_427436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 3].length) (baseStart_427436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_427436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_427436 prefixEnd_427436 := by exact prefixLift 427436
  have htrace : WordTrace (prefixWord ++ tailWord_427436) baseStart_427436 baseEnd_427436 := by
    simpa [prefixWord, tailWord_427436, baseEnd_427436] using wordTrace_append hprefix tailTrace_427436
  have hstable : (prefixWord ++ tailWord_427436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427436).length < 2 ^ (prefixWord ++ tailWord_427436).sum := by decide
  have hdescent : baseEnd_427436 < baseStart_427436 := by decide
  rcases family_descends (prefixWord ++ tailWord_427436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427453 : List Nat := [1, 4, 1, 2, 2, 1, 3, 3, 2, 3]
def baseStart_427453 : Nat := 118140960795 + 427453 * 2 ^ 59
def prefixEnd_427453 : Nat := 4983230072969 + 3 ^ 40 * 427453 * 2
def baseEnd_427453 : Nat := 146325897470947547914457

theorem tailTrace_427453 : CollatzResearch.WordTrace tailWord_427453 prefixEnd_427453 146325897470947547914457 := by
  unfold tailWord_427453
  simp only [CollatzResearch.WordTrace]
  refine ⟨15590491720418259005431013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10393661146945506003620675 15590491720418259005431013)
  ·
    refine ⟨2923217197578423563518315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15590491720418259005431013 2923217197578423563518315)
    ·
      refine ⟨4384825796367635345277473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2923217197578423563518315 4384825796367635345277473)
      ·
        refine ⟨3288619347275726508958105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4384825796367635345277473 3288619347275726508958105)
        ·
          refine ⟨2466464510456794881718579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3288619347275726508958105 2466464510456794881718579)
          ·
            refine ⟨3699696765685192322577869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2466464510456794881718579 3699696765685192322577869)
            ·
              refine ⟨1387386287131947120966701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3699696765685192322577869 1387386287131947120966701)
              ·
                refine ⟨520269857674480170362513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1387386287131947120966701 520269857674480170362513)
                ·
                  refine ⟨390202393255860127771885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 520269857674480170362513 390202393255860127771885)
                  ·
                    refine ⟨146325897470947547914457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 390202393255860127771885 146325897470947547914457)
                    ·
                      rfl

theorem cell22_427453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_427453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_427453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_427453 prefixEnd_427453 := by exact prefixLift 427453
  have htrace : WordTrace (prefixWord ++ tailWord_427453) baseStart_427453 baseEnd_427453 := by
    simpa [prefixWord, tailWord_427453, baseEnd_427453] using wordTrace_append hprefix tailTrace_427453
  have hstable : (prefixWord ++ tailWord_427453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427453).length < 2 ^ (prefixWord ++ tailWord_427453).sum := by decide
  have hdescent : baseEnd_427453 < baseStart_427453 := by decide
  rcases family_descends (prefixWord ++ tailWord_427453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427468 : List Nat := [2, 2, 1, 4, 2, 2, 2, 1, 2, 4]
def baseStart_427468 : Nat := 118140960795 + 427468 * 2 ^ 59
def prefixEnd_427468 : Nat := 4983230072969 + 3 ^ 40 * 427468 * 2
def baseEnd_427468 : Nat := 146331032277492508789411

theorem tailTrace_427468 : CollatzResearch.WordTrace tailWord_427468 prefixEnd_427468 146331032277492508789411 := by
  unfold tailWord_427468
  simp only [CollatzResearch.WordTrace]
  refine ⟨7795519407681958283613529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10394025876909277711484705 7795519407681958283613529)
  ·
    refine ⟨5846639555761468712710147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7795519407681958283613529 5846639555761468712710147)
    ·
      refine ⟨8769959333642203069065221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5846639555761468712710147 8769959333642203069065221)
      ·
        refine ⟨1644367375057913075449729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8769959333642203069065221 1644367375057913075449729)
        ·
          refine ⟨1233275531293434806587297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1644367375057913075449729 1233275531293434806587297)
          ·
            refine ⟨924956648470076104940473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1233275531293434806587297 924956648470076104940473)
            ·
              refine ⟨693717486352557078705355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 924956648470076104940473 693717486352557078705355)
              ·
                refine ⟨1040576229528835618058033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 693717486352557078705355 1040576229528835618058033)
                ·
                  refine ⟨780432172146626713543525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1040576229528835618058033 780432172146626713543525)
                  ·
                    refine ⟨146331032277492508789411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 780432172146626713543525 146331032277492508789411)
                    ·
                      rfl

theorem cell22_427468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 2, 4].length) (baseStart_427468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_427468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_427468 prefixEnd_427468 := by exact prefixLift 427468
  have htrace : WordTrace (prefixWord ++ tailWord_427468) baseStart_427468 baseEnd_427468 := by
    simpa [prefixWord, tailWord_427468, baseEnd_427468] using wordTrace_append hprefix tailTrace_427468
  have hstable : (prefixWord ++ tailWord_427468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427468).length < 2 ^ (prefixWord ++ tailWord_427468).sum := by decide
  have hdescent : baseEnd_427468 < baseStart_427468 := by decide
  rcases family_descends (prefixWord ++ tailWord_427468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427479 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 4, 6]
def baseStart_427479 : Nat := 118140960795 + 427479 * 2 ^ 59
def prefixEnd_427479 : Nat := 4983230072969 + 3 ^ 40 * 427479 * 2
def baseEnd_427479 : Nat := 146334797802292146764377

theorem tailTrace_427479 : CollatzResearch.WordTrace tailWord_427479 prefixEnd_427479 146334797802292146764377 := by
  unfold tailWord_427479
  simp only [CollatzResearch.WordTrace]
  refine ⟨15591440018324065445877491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10394293345549376963918327 15591440018324065445877491)
  ·
    refine ⟨23387160027486098168816237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15591440018324065445877491 23387160027486098168816237)
    ·
      refine ⟨8770185010307286813306089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23387160027486098168816237 8770185010307286813306089)
      ·
        refine ⟨6577638757730465109979567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8770185010307286813306089 6577638757730465109979567)
        ·
          refine ⟨9866458136595697664969351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6577638757730465109979567 9866458136595697664969351)
          ·
            refine ⟨14799687204893546497454027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9866458136595697664969351 14799687204893546497454027)
            ·
              refine ⟨22199530807340319746181041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14799687204893546497454027 22199530807340319746181041)
              ·
                refine ⟨16649648105505239809635781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22199530807340319746181041 16649648105505239809635781)
                ·
                  refine ⟨3121809019782232464306709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16649648105505239809635781 3121809019782232464306709)
                  ·
                    refine ⟨146334797802292146764377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3121809019782232464306709 146334797802292146764377)
                    ·
                      rfl

theorem cell22_427479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_427479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_427479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_427479 prefixEnd_427479 := by exact prefixLift 427479
  have htrace : WordTrace (prefixWord ++ tailWord_427479) baseStart_427479 baseEnd_427479 := by
    simpa [prefixWord, tailWord_427479, baseEnd_427479] using wordTrace_append hprefix tailTrace_427479
  have hstable : (prefixWord ++ tailWord_427479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427479).length < 2 ^ (prefixWord ++ tailWord_427479).sum := by decide
  have hdescent : baseEnd_427479 < baseStart_427479 := by decide
  rcases family_descends (prefixWord ++ tailWord_427479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427532 : List Nat := [2, 2, 1, 2, 5, 1, 2, 3, 1, 3]
def baseStart_427532 : Nat := 118140960795 + 427532 * 2 ^ 59
def prefixEnd_427532 : Nat := 4983230072969 + 3 ^ 40 * 427532 * 2
def baseEnd_427532 : Nat := 146352940785417675189215

theorem tailTrace_427532 : CollatzResearch.WordTrace tailWord_427532 prefixEnd_427532 146352940785417675189215 := by
  unfold tailWord_427532
  simp only [CollatzResearch.WordTrace]
  refine ⟨7796686543566027748778425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10395582058088036998371233 7796686543566027748778425)
  ·
    refine ⟨5847514907674520811583819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7796686543566027748778425 5847514907674520811583819)
    ·
      refine ⟨8771272361511781217375729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5847514907674520811583819 8771272361511781217375729)
      ·
        refine ⟨6578454271133835913031797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8771272361511781217375729 6578454271133835913031797)
        ·
          refine ⟨616730087918797116846731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6578454271133835913031797 616730087918797116846731)
          ·
            refine ⟨925095131878195675270097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616730087918797116846731 925095131878195675270097)
            ·
              refine ⟨693821348908646756452573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 925095131878195675270097 693821348908646756452573)
              ·
                refine ⟨260183005840742533669715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 693821348908646756452573 260183005840742533669715)
                ·
                  refine ⟨390274508761113800504573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 260183005840742533669715 390274508761113800504573)
                  ·
                    refine ⟨146352940785417675189215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 390274508761113800504573 146352940785417675189215)
                    ·
                      rfl

theorem cell22_427532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 3, 1, 3].length) (baseStart_427532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_427532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_427532 prefixEnd_427532 := by exact prefixLift 427532
  have htrace : WordTrace (prefixWord ++ tailWord_427532) baseStart_427532 baseEnd_427532 := by
    simpa [prefixWord, tailWord_427532, baseEnd_427532] using wordTrace_append hprefix tailTrace_427532
  have hstable : (prefixWord ++ tailWord_427532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427532).length < 2 ^ (prefixWord ++ tailWord_427532).sum := by decide
  have hdescent : baseEnd_427532 < baseStart_427532 := by decide
  rcases family_descends (prefixWord ++ tailWord_427532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427633 : List Nat := [1, 2, 2, 2, 1, 1, 1, 6, 3, 3]
def baseStart_427633 : Nat := 118140960795 + 427633 * 2 ^ 59
def prefixEnd_427633 : Nat := 4983230072969 + 3 ^ 40 * 427633 * 2
def baseEnd_427633 : Nat := 146387515149487078413905

theorem tailTrace_427633 : CollatzResearch.WordTrace tailWord_427633 prefixEnd_427633 146387515149487078413905 := by
  unfold tailWord_427633
  simp only [CollatzResearch.WordTrace]
  refine ⟨15597056859766149746983553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10398037906510766497989035 15597056859766149746983553)
  ·
    refine ⟨11697792644824612310237665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15597056859766149746983553 11697792644824612310237665)
    ·
      refine ⟨8773344483618459232678249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11697792644824612310237665 8773344483618459232678249)
      ·
        refine ⟨6580008362713844424508687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8773344483618459232678249 6580008362713844424508687)
        ·
          refine ⟨9870012544070766636763031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6580008362713844424508687 9870012544070766636763031)
          ·
            refine ⟨14805018816106149955144547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9870012544070766636763031 14805018816106149955144547)
            ·
              refine ⟨22207528224159224932716821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14805018816106149955144547 22207528224159224932716821)
              ·
                refine ⟨1040977885507463668721101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22207528224159224932716821 1040977885507463668721101)
                ·
                  refine ⟨390366707065298875770413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1040977885507463668721101 390366707065298875770413)
                  ·
                    refine ⟨146387515149487078413905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 390366707065298875770413 146387515149487078413905)
                    ·
                      rfl

theorem cell22_427633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 3, 3].length) (baseStart_427633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_427633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_427633 prefixEnd_427633 := by exact prefixLift 427633
  have htrace : WordTrace (prefixWord ++ tailWord_427633) baseStart_427633 baseEnd_427633 := by
    simpa [prefixWord, tailWord_427633, baseEnd_427633] using wordTrace_append hprefix tailTrace_427633
  have hstable : (prefixWord ++ tailWord_427633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427633).length < 2 ^ (prefixWord ++ tailWord_427633).sum := by decide
  have hdescent : baseEnd_427633 < baseStart_427633 := by decide
  rcases family_descends (prefixWord ++ tailWord_427633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427714 : List Nat := [3, 5, 1, 2, 1, 1, 1, 1, 7]
def baseStart_427714 : Nat := 118140960795 + 427714 * 2 ^ 59
def prefixEnd_427714 : Nat := 4983230072969 + 3 ^ 40 * 427714 * 2
def baseEnd_427714 : Nat := 48805081034943289046219

theorem tailTrace_427714 : CollatzResearch.WordTrace tailWord_427714 prefixEnd_427714 48805081034943289046219 := by
  unfold tailWord_427714
  simp only [CollatzResearch.WordTrace]
  refine ⟨3900002793118175145170549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10400007448315133720454797 3900002793118175145170549)
  ·
    refine ⟨365625261854828919859739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3900002793118175145170549 365625261854828919859739)
    ·
      refine ⟨548437892782243379789609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365625261854828919859739 548437892782243379789609)
      ·
        refine ⟨411328419586682534842207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 548437892782243379789609 411328419586682534842207)
        ·
          refine ⟨616992629380023802263311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411328419586682534842207 616992629380023802263311)
          ·
            refine ⟨925488944070035703394967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616992629380023802263311 925488944070035703394967)
            ·
              refine ⟨1388233416105053555092451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 925488944070035703394967 1388233416105053555092451)
              ·
                refine ⟨2082350124157580332638677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1388233416105053555092451 2082350124157580332638677)
                ·
                  refine ⟨48805081034943289046219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2082350124157580332638677 48805081034943289046219)
                  ·
                    rfl

theorem cell22_427714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_427714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_427714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_427714 prefixEnd_427714 := by exact prefixLift 427714
  have htrace : WordTrace (prefixWord ++ tailWord_427714) baseStart_427714 baseEnd_427714 := by
    simpa [prefixWord, tailWord_427714, baseEnd_427714] using wordTrace_append hprefix tailTrace_427714
  have hstable : (prefixWord ++ tailWord_427714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427714).length < 2 ^ (prefixWord ++ tailWord_427714).sum := by decide
  have hdescent : baseEnd_427714 < baseStart_427714 := by decide
  rcases family_descends (prefixWord ++ tailWord_427714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427738 : List Nat := [3, 1, 1, 2, 2, 3, 1, 2, 1, 6]
def baseStart_427738 : Nat := 118140960795 + 427738 * 2 ^ 59
def prefixEnd_427738 : Nat := 4983230072969 + 3 ^ 40 * 427738 * 2
def baseEnd_427738 : Nat := 146423458795301804538583

theorem tailTrace_427738 : CollatzResearch.WordTrace tailWord_427738 prefixEnd_427738 146423458795301804538583 := by
  unfold tailWord_427738
  simp only [CollatzResearch.WordTrace]
  refine ⟨3900221631096438169888967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10400591016257168453037245 3900221631096438169888967)
  ·
    refine ⟨5850332446644657254833451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3900221631096438169888967 5850332446644657254833451)
    ·
      refine ⟨8775498669966985882250177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5850332446644657254833451 8775498669966985882250177)
      ·
        refine ⟨6581624002475239411687633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8775498669966985882250177 6581624002475239411687633)
        ·
          refine ⟨4936218001856429558765725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6581624002475239411687633 4936218001856429558765725)
          ·
            refine ⟨1851081750696161084537147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4936218001856429558765725 1851081750696161084537147)
            ·
              refine ⟨2776622626044241626805721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1851081750696161084537147 2776622626044241626805721)
              ·
                refine ⟨2082466969533181220104291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2776622626044241626805721 2082466969533181220104291)
                ·
                  refine ⟨3123700454299771830156437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2082466969533181220104291 3123700454299771830156437)
                  ·
                    refine ⟨146423458795301804538583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3123700454299771830156437 146423458795301804538583)
                    ·
                      rfl

theorem cell22_427738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_427738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_427738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_427738 prefixEnd_427738 := by exact prefixLift 427738
  have htrace : WordTrace (prefixWord ++ tailWord_427738) baseStart_427738 baseEnd_427738 := by
    simpa [prefixWord, tailWord_427738, baseEnd_427738] using wordTrace_append hprefix tailTrace_427738
  have hstable : (prefixWord ++ tailWord_427738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427738).length < 2 ^ (prefixWord ++ tailWord_427738).sum := by decide
  have hdescent : baseEnd_427738 < baseStart_427738 := by decide
  rcases family_descends (prefixWord ++ tailWord_427738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427782 : List Nat := [6, 2, 2, 1, 2, 1, 2, 1, 5]
def baseStart_427782 : Nat := 118140960795 + 427782 * 2 ^ 59
def prefixEnd_427782 : Nat := 4983230072969 + 3 ^ 40 * 427782 * 2
def baseEnd_427782 : Nat := 48812840298166785479483

theorem tailTrace_427782 : CollatzResearch.WordTrace tailWord_427782 prefixEnd_427782 48812840298166785479483 := by
  unfold tailWord_427782
  simp only [CollatzResearch.WordTrace]
  refine ⟨487577854257073381067425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10401660890817565462771733 487577854257073381067425)
  ·
    refine ⟨365683390692805035800569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 487577854257073381067425 365683390692805035800569)
    ·
      refine ⟨274262543019603776850427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365683390692805035800569 274262543019603776850427)
      ·
        refine ⟨411393814529405665275641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274262543019603776850427 411393814529405665275641)
        ·
          refine ⟨308545360897054248956731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411393814529405665275641 308545360897054248956731)
          ·
            refine ⟨462818041345581373435097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308545360897054248956731 462818041345581373435097)
            ·
              refine ⟨347113531009186030076323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 462818041345581373435097 347113531009186030076323)
              ·
                refine ⟨520670296513779045114485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 347113531009186030076323 520670296513779045114485)
                ·
                  refine ⟨48812840298166785479483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 520670296513779045114485 48812840298166785479483)
                  ·
                    rfl

theorem cell22_427782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_427782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_427782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_427782 prefixEnd_427782 := by exact prefixLift 427782
  have htrace : WordTrace (prefixWord ++ tailWord_427782) baseStart_427782 baseEnd_427782 := by
    simpa [prefixWord, tailWord_427782, baseEnd_427782] using wordTrace_append hprefix tailTrace_427782
  have hstable : (prefixWord ++ tailWord_427782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427782).length < 2 ^ (prefixWord ++ tailWord_427782).sum := by decide
  have hdescent : baseEnd_427782 < baseStart_427782 := by decide
  rcases family_descends (prefixWord ++ tailWord_427782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427806 : List Nat := [4, 3, 2, 2, 1, 1, 2, 1, 2, 4]
def baseStart_427806 : Nat := 118140960795 + 427806 * 2 ^ 59
def prefixEnd_427806 : Nat := 4983230072969 + 3 ^ 40 * 427806 * 2
def baseEnd_427806 : Nat := 146446736584972293838375

theorem tailTrace_427806 : CollatzResearch.WordTrace tailWord_427806 prefixEnd_427806 146446736584972293838375 := by
  unfold tailWord_427806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1950420836017425036628909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10402244458759600195354181 1950420836017425036628909)
  ·
    refine ⟨731407813506534388735841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1950420836017425036628909 731407813506534388735841)
    ·
      refine ⟨548555860129900791551881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 731407813506534388735841 548555860129900791551881)
      ·
        refine ⟨411416895097425593663911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 548555860129900791551881 411416895097425593663911)
        ·
          refine ⟨617125342646138390495867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411416895097425593663911 617125342646138390495867)
          ·
            refine ⟨925688013969207585743801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617125342646138390495867 925688013969207585743801)
            ·
              refine ⟨694266010476905689307851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 925688013969207585743801 694266010476905689307851)
              ·
                refine ⟨1041399015715358533961777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 694266010476905689307851 1041399015715358533961777)
                ·
                  refine ⟨781049261786518900471333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1041399015715358533961777 781049261786518900471333)
                  ·
                    refine ⟨146446736584972293838375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 781049261786518900471333 146446736584972293838375)
                    ·
                      rfl

theorem cell22_427806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_427806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_427806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_427806 prefixEnd_427806 := by exact prefixLift 427806
  have htrace : WordTrace (prefixWord ++ tailWord_427806) baseStart_427806 baseEnd_427806 := by
    simpa [prefixWord, tailWord_427806, baseEnd_427806] using wordTrace_append hprefix tailTrace_427806
  have hstable : (prefixWord ++ tailWord_427806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427806).length < 2 ^ (prefixWord ++ tailWord_427806).sum := by decide
  have hdescent : baseEnd_427806 < baseStart_427806 := by decide
  rcases family_descends (prefixWord ++ tailWord_427806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427860 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 8]
def baseStart_427860 : Nat := 118140960795 + 427860 * 2 ^ 59
def prefixEnd_427860 : Nat := 4983230072969 + 3 ^ 40 * 427860 * 2
def baseEnd_427860 : Nat := 48821740629511384329403

theorem tailTrace_427860 : CollatzResearch.WordTrace tailWord_427860 prefixEnd_427860 48821740629511384329403 := by
  unfold tailWord_427860
  simp only [CollatzResearch.WordTrace]
  refine ⟨7802668114971883757748517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10403557486629178343664689 7802668114971883757748517)
  ·
    refine ⟨1463000271557228204577847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7802668114971883757748517 1463000271557228204577847)
    ·
      refine ⟨2194500407335842306866771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1463000271557228204577847 2194500407335842306866771)
      ·
        refine ⟨3291750611003763460300157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2194500407335842306866771 3291750611003763460300157)
        ·
          refine ⟨1234406479126411297612559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3291750611003763460300157 1234406479126411297612559)
          ·
            refine ⟨1851609718689616946418839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1234406479126411297612559 1851609718689616946418839)
            ·
              refine ⟨2777414578034425419628259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1851609718689616946418839 2777414578034425419628259)
              ·
                refine ⟨4166121867051638129442389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2777414578034425419628259 4166121867051638129442389)
                ·
                  refine ⟨48821740629511384329403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4166121867051638129442389 48821740629511384329403)
                  ·
                    rfl

theorem cell22_427860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_427860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_427860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_427860 prefixEnd_427860 := by exact prefixLift 427860
  have htrace : WordTrace (prefixWord ++ tailWord_427860) baseStart_427860 baseEnd_427860 := by
    simpa [prefixWord, tailWord_427860, baseEnd_427860] using wordTrace_append hprefix tailTrace_427860
  have hstable : (prefixWord ++ tailWord_427860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427860).length < 2 ^ (prefixWord ++ tailWord_427860).sum := by decide
  have hdescent : baseEnd_427860 < baseStart_427860 := by decide
  rcases family_descends (prefixWord ++ tailWord_427860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427890 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 4, 4]
def baseStart_427890 : Nat := 118140960795 + 427890 * 2 ^ 59
def prefixEnd_427890 : Nat := 4983230072969 + 3 ^ 40 * 427890 * 2
def baseEnd_427890 : Nat := 146475491501624074738117

theorem tailTrace_427890 : CollatzResearch.WordTrace tailWord_427890 prefixEnd_427890 146475491501624074738117 := by
  unfold tailWord_427890
  simp only [CollatzResearch.WordTrace]
  refine ⟨3901607604958770659772281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10404286946556721759392749 3901607604958770659772281)
  ·
    refine ⟨2926205703719077994829211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3901607604958770659772281 2926205703719077994829211)
    ·
      refine ⟨4389308555578616992243817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2926205703719077994829211 4389308555578616992243817)
      ·
        refine ⟨3291981416683962744182863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4389308555578616992243817 3291981416683962744182863)
        ·
          refine ⟨4937972125025944116274295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3291981416683962744182863 4937972125025944116274295)
          ·
            refine ⟨7406958187538916174411443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4937972125025944116274295 7406958187538916174411443)
            ·
              refine ⟨11110437281308374261617165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7406958187538916174411443 11110437281308374261617165)
              ·
                refine ⟨4166413980490640348106437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11110437281308374261617165 4166413980490640348106437)
                ·
                  refine ⟨781202621341995065269957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4166413980490640348106437 781202621341995065269957)
                  ·
                    refine ⟨146475491501624074738117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 781202621341995065269957 146475491501624074738117)
                    ·
                      rfl

theorem cell22_427890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_427890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_427890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_427890 prefixEnd_427890 := by exact prefixLift 427890
  have htrace : WordTrace (prefixWord ++ tailWord_427890) baseStart_427890 baseEnd_427890 := by
    simpa [prefixWord, tailWord_427890, baseEnd_427890] using wordTrace_append hprefix tailTrace_427890
  have hstable : (prefixWord ++ tailWord_427890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427890).length < 2 ^ (prefixWord ++ tailWord_427890).sum := by decide
  have hdescent : baseEnd_427890 < baseStart_427890 := by decide
  rcases family_descends (prefixWord ++ tailWord_427890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427894 : List Nat := [5, 1, 1, 3, 2, 1, 2, 1, 6]
def baseStart_427894 : Nat := 118140960795 + 427894 * 2 ^ 59
def prefixEnd_427894 : Nat := 4983230072969 + 3 ^ 40 * 427894 * 2
def baseEnd_427894 : Nat := 48825620261123132546035

theorem tailTrace_427894 : CollatzResearch.WordTrace tailWord_427894 prefixEnd_427894 48825620261123132546035 := by
  unfold tailWord_427894
  simp only [CollatzResearch.WordTrace]
  refine ⟨975411019488786957639671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10404384207880394214823157 975411019488786957639671)
  ·
    refine ⟨1463116529233180436459507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 975411019488786957639671 1463116529233180436459507)
    ·
      refine ⟨2194674793849770654689261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1463116529233180436459507 2194674793849770654689261)
      ·
        refine ⟨823003047693663995508473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2194674793849770654689261 823003047693663995508473)
        ·
          refine ⟨617252285770247996631355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 823003047693663995508473 617252285770247996631355)
          ·
            refine ⟨925878428655371994947033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617252285770247996631355 925878428655371994947033)
            ·
              refine ⟨694408821491528996210275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 925878428655371994947033 694408821491528996210275)
              ·
                refine ⟨1041613232237293494315413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 694408821491528996210275 1041613232237293494315413)
                ·
                  refine ⟨48825620261123132546035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1041613232237293494315413 48825620261123132546035)
                  ·
                    rfl

theorem cell22_427894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_427894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_427894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_427894 prefixEnd_427894 := by exact prefixLift 427894
  have htrace : WordTrace (prefixWord ++ tailWord_427894) baseStart_427894 baseEnd_427894 := by
    simpa [prefixWord, tailWord_427894, baseEnd_427894] using wordTrace_append hprefix tailTrace_427894
  have hstable : (prefixWord ++ tailWord_427894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427894).length < 2 ^ (prefixWord ++ tailWord_427894).sum := by decide
  have hdescent : baseEnd_427894 < baseStart_427894 := by decide
  rcases family_descends (prefixWord ++ tailWord_427894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427909 : List Nat := [1, 3, 1, 1, 3, 2, 5, 1, 2, 3]
def baseStart_427909 : Nat := 118140960795 + 427909 * 2 ^ 59
def prefixEnd_427909 : Nat := 4983230072969 + 3 ^ 40 * 427909 * 2
def baseEnd_427909 : Nat := 146481995589914358513059

theorem tailTrace_427909 : CollatzResearch.WordTrace tailWord_427909 prefixEnd_427909 146481995589914358513059 := by
  unfold tailWord_427909
  simp only [CollatzResearch.WordTrace]
  refine ⟨15607123406766248884030781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10404748937844165922687187 15607123406766248884030781)
  ·
    refine ⟨5852671277537343331511543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15607123406766248884030781 5852671277537343331511543)
    ·
      refine ⟨8779006916306014997267315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5852671277537343331511543 8779006916306014997267315)
      ·
        refine ⟨13168510374459022495900973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8779006916306014997267315 13168510374459022495900973)
        ·
          refine ⟨4938191390422133435962865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13168510374459022495900973 4938191390422133435962865)
          ·
            refine ⟨3703643542816600076972149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4938191390422133435962865 3703643542816600076972149)
            ·
              refine ⟨347216582139056257216139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3703643542816600076972149 347216582139056257216139)
              ·
                refine ⟨520824873208584385824209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 347216582139056257216139 520824873208584385824209)
                ·
                  refine ⟨390618654906438289368157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 520824873208584385824209 390618654906438289368157)
                  ·
                    refine ⟨146481995589914358513059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 390618654906438289368157 146481995589914358513059)
                    ·
                      rfl

theorem cell22_427909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 2, 3].length) (baseStart_427909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_427909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_427909 prefixEnd_427909 := by exact prefixLift 427909
  have htrace : WordTrace (prefixWord ++ tailWord_427909) baseStart_427909 baseEnd_427909 := by
    simpa [prefixWord, tailWord_427909, baseEnd_427909] using wordTrace_append hprefix tailTrace_427909
  have hstable : (prefixWord ++ tailWord_427909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427909).length < 2 ^ (prefixWord ++ tailWord_427909).sum := by decide
  have hdescent : baseEnd_427909 < baseStart_427909 := by decide
  rcases family_descends (prefixWord ++ tailWord_427909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427922 : List Nat := [3, 2, 3, 2, 1, 2, 1, 8]
def baseStart_427922 : Nat := 118140960795 + 427922 * 2 ^ 59
def prefixEnd_427922 : Nat := 4983230072969 + 3 ^ 40 * 427922 * 2
def baseEnd_427922 : Nat := 16276271750620739770891

theorem tailTrace_427922 : CollatzResearch.WordTrace tailWord_427922 prefixEnd_427922 16276271750620739770891 := by
  unfold tailWord_427922
  simp only [CollatzResearch.WordTrace]
  refine ⟨3901899388929788026063505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10405065037146101402836013 3901899388929788026063505)
  ·
    refine ⟨2926424541697341019547629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3901899388929788026063505 2926424541697341019547629)
    ·
      refine ⟨1097409203136502882330361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2926424541697341019547629 1097409203136502882330361)
      ·
        refine ⟨823056902352377161747771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1097409203136502882330361 823056902352377161747771)
        ·
          refine ⟨1234585353528565742621657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 823056902352377161747771 1234585353528565742621657)
          ·
            refine ⟨925939015146424306966243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1234585353528565742621657 925939015146424306966243)
            ·
              refine ⟨1388908522719636460449365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 925939015146424306966243 1388908522719636460449365)
              ·
                refine ⟨16276271750620739770891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1388908522719636460449365 16276271750620739770891)
                ·
                  rfl

theorem cell22_427922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 8].length) (baseStart_427922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_427922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_427922 prefixEnd_427922 := by exact prefixLift 427922
  have htrace : WordTrace (prefixWord ++ tailWord_427922) baseStart_427922 baseEnd_427922 := by
    simpa [prefixWord, tailWord_427922, baseEnd_427922] using wordTrace_append hprefix tailTrace_427922
  have hstable : (prefixWord ++ tailWord_427922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427922).length < 2 ^ (prefixWord ++ tailWord_427922).sum := by decide
  have hdescent : baseEnd_427922 < baseStart_427922 := by decide
  rcases family_descends (prefixWord ++ tailWord_427922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427928 : List Nat := [2, 1, 2, 6, 2, 1, 1, 3, 4]
def baseStart_427928 : Nat := 118140960795 + 427928 * 2 ^ 59
def prefixEnd_427928 : Nat := 4983230072969 + 3 ^ 40 * 427928 * 2
def baseEnd_427928 : Nat := 48829499892734880762667

theorem tailTrace_427928 : CollatzResearch.WordTrace tailWord_427928 prefixEnd_427928 48829499892734880762667 := by
  unfold tailWord_427928
  simp only [CollatzResearch.WordTrace]
  refine ⟨7803908196848707564486219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10405210929131610085981625 7803908196848707564486219)
  ·
    refine ⟨11705862295273061346729329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7803908196848707564486219 11705862295273061346729329)
    ·
      refine ⟨8779396721454796010046997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11705862295273061346729329 8779396721454796010046997)
      ·
        refine ⟨411534221318193562970953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8779396721454796010046997 411534221318193562970953)
        ·
          refine ⟨308650665988645172228215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411534221318193562970953 308650665988645172228215)
          ·
            refine ⟨462975998982967758342323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308650665988645172228215 462975998982967758342323)
            ·
              refine ⟨694463998474451637513485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462975998982967758342323 694463998474451637513485)
              ·
                refine ⟨260423999427919364067557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 694463998474451637513485 260423999427919364067557)
                ·
                  refine ⟨48829499892734880762667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 260423999427919364067557 48829499892734880762667)
                  ·
                    rfl

theorem cell22_427928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 3, 4].length) (baseStart_427928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_427928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_427928 prefixEnd_427928 := by exact prefixLift 427928
  have htrace : WordTrace (prefixWord ++ tailWord_427928) baseStart_427928 baseEnd_427928 := by
    simpa [prefixWord, tailWord_427928, baseEnd_427928] using wordTrace_append hprefix tailTrace_427928
  have hstable : (prefixWord ++ tailWord_427928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427928).length < 2 ^ (prefixWord ++ tailWord_427928).sum := by decide
  have hdescent : baseEnd_427928 < baseStart_427928 := by decide
  rcases family_descends (prefixWord ++ tailWord_427928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_427954 : List Nat := [3, 2, 1, 1, 1, 1, 1, 8, 1, 3]
def baseStart_427954 : Nat := 118140960795 + 427954 * 2 ^ 59
def prefixEnd_427954 : Nat := 4983230072969 + 3 ^ 40 * 427954 * 2
def baseEnd_427954 : Nat := 146497400009549241137921

theorem tailTrace_427954 : CollatzResearch.WordTrace tailWord_427954 prefixEnd_427954 146497400009549241137921 := by
  unfold tailWord_427954
  simp only [CollatzResearch.WordTrace]
  refine ⟨3902191172900805392354729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10405843127735481046279277 3902191172900805392354729)
  ·
    refine ⟨2926643379675604044266047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3902191172900805392354729 2926643379675604044266047)
    ·
      refine ⟨4389965069513406066399071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2926643379675604044266047 4389965069513406066399071)
      ·
        refine ⟨6584947604270109099598607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4389965069513406066399071 6584947604270109099598607)
        ·
          refine ⟨9877421406405163649397911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6584947604270109099598607 9877421406405163649397911)
          ·
            refine ⟨14816132109607745474096867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9877421406405163649397911 14816132109607745474096867)
            ·
              refine ⟨22224198164411618211145301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14816132109607745474096867 22224198164411618211145301)
              ·
                refine ⟨260439822239198650911859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 22224198164411618211145301 260439822239198650911859)
                ·
                  refine ⟨390659733358797976367789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 260439822239198650911859 390659733358797976367789)
                  ·
                    refine ⟨146497400009549241137921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 390659733358797976367789 146497400009549241137921)
                    ·
                      rfl

theorem cell22_427954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 8, 1, 3].length) (baseStart_427954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_427954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_427954 prefixEnd_427954 := by exact prefixLift 427954
  have htrace : WordTrace (prefixWord ++ tailWord_427954) baseStart_427954 baseEnd_427954 := by
    simpa [prefixWord, tailWord_427954, baseEnd_427954] using wordTrace_append hprefix tailTrace_427954
  have hstable : (prefixWord ++ tailWord_427954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_427954).length < 2 ^ (prefixWord ++ tailWord_427954).sum := by decide
  have hdescent : baseEnd_427954 < baseStart_427954 := by decide
  rcases family_descends (prefixWord ++ tailWord_427954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428061 : List Nat := [1, 4, 2, 2, 2, 1, 3, 2, 2, 3]
def baseStart_428061 : Nat := 118140960795 + 428061 * 2 ^ 59
def prefixEnd_428061 : Nat := 4983230072969 + 3 ^ 40 * 428061 * 2
def baseEnd_428061 : Nat := 146534028296236628712593

theorem tailTrace_428061 : CollatzResearch.WordTrace tailWord_428061 prefixEnd_428061 146534028296236628712593 := by
  unfold tailWord_428061
  simp only [CollatzResearch.WordTrace]
  refine ⟨15612667302215578843564037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10408444868143719229042691 15612667302215578843564037)
  ·
    refine ⟨2927375119165421033168257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15612667302215578843564037 2927375119165421033168257)
    ·
      refine ⟨2195531339374065774876193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2927375119165421033168257 2195531339374065774876193)
      ·
        refine ⟨1646648504530549331157145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2195531339374065774876193 1646648504530549331157145)
        ·
          refine ⟨1234986378397911998367859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1646648504530549331157145 1234986378397911998367859)
          ·
            refine ⟨1852479567596867997551789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1234986378397911998367859 1852479567596867997551789)
            ·
              refine ⟨694679837848825499081921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1852479567596867997551789 694679837848825499081921)
              ·
                refine ⟨521009878386619124311441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 694679837848825499081921 521009878386619124311441)
                ·
                  refine ⟨390757408789964343233581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 521009878386619124311441 390757408789964343233581)
                  ·
                    refine ⟨146534028296236628712593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 390757408789964343233581 146534028296236628712593)
                    ·
                      rfl

theorem cell22_428061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_428061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_428061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_428061 prefixEnd_428061 := by exact prefixLift 428061
  have htrace : WordTrace (prefixWord ++ tailWord_428061) baseStart_428061 baseEnd_428061 := by
    simpa [prefixWord, tailWord_428061, baseEnd_428061] using wordTrace_append hprefix tailTrace_428061
  have hstable : (prefixWord ++ tailWord_428061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428061).length < 2 ^ (prefixWord ++ tailWord_428061).sum := by decide
  have hdescent : baseEnd_428061 < baseStart_428061 := by decide
  rcases family_descends (prefixWord ++ tailWord_428061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428078 : List Nat := [4, 1, 3, 1, 1, 3, 3, 1, 2, 3]
def baseStart_428078 : Nat := 118140960795 + 428078 * 2 ^ 59
def prefixEnd_428078 : Nat := 4983230072969 + 3 ^ 40 * 428078 * 2
def baseEnd_428078 : Nat := 146539847743654251037541

theorem tailTrace_428078 : CollatzResearch.WordTrace tailWord_428078 prefixEnd_428078 146539847743654251037541 := by
  unfold tailWord_428078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1951660917894248843366611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10408858228769327164621925 1951660917894248843366611)
  ·
    refine ⟨2927491376841373265049917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1951660917894248843366611 2927491376841373265049917)
    ·
      refine ⟨1097809266315514974393719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2927491376841373265049917 1097809266315514974393719)
      ·
        refine ⟨1646713899473272461590579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1097809266315514974393719 1646713899473272461590579)
        ·
          refine ⟨2470070849209908692385869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1646713899473272461590579 2470070849209908692385869)
          ·
            refine ⟨926276568453715759644701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2470070849209908692385869 926276568453715759644701)
            ·
              refine ⟨347353713170143409866763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 926276568453715759644701 347353713170143409866763)
              ·
                refine ⟨521030569755215114800145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 347353713170143409866763 521030569755215114800145)
                ·
                  refine ⟨390772927316411336100109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 521030569755215114800145 390772927316411336100109)
                  ·
                    refine ⟨146539847743654251037541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 390772927316411336100109 146539847743654251037541)
                    ·
                      rfl

theorem cell22_428078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_428078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_428078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_428078 prefixEnd_428078 := by exact prefixLift 428078
  have htrace : WordTrace (prefixWord ++ tailWord_428078) baseStart_428078 baseEnd_428078 := by
    simpa [prefixWord, tailWord_428078, baseEnd_428078] using wordTrace_append hprefix tailTrace_428078
  have hstable : (prefixWord ++ tailWord_428078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428078).length < 2 ^ (prefixWord ++ tailWord_428078).sum := by decide
  have hdescent : baseEnd_428078 < baseStart_428078 := by decide
  rcases family_descends (prefixWord ++ tailWord_428078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428196 : List Nat := [2, 3, 1, 2, 4, 1, 2, 1, 1, 5]
def baseStart_428196 : Nat := 118140960795 + 428196 * 2 ^ 59
def prefixEnd_428196 : Nat := 4983230072969 + 3 ^ 40 * 428196 * 2
def baseEnd_428196 : Nat := 146580241555141276587179

theorem tailTrace_428196 : CollatzResearch.WordTrace tailWord_428196 prefixEnd_428196 146580241555141276587179 := by
  unfold tailWord_428196
  simp only [CollatzResearch.WordTrace]
  refine ⟨7808795578363248449864221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10411727437817664599818961 7808795578363248449864221)
  ·
    refine ⟨2928298341886218168699083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7808795578363248449864221 2928298341886218168699083)
    ·
      refine ⟨4392447512829327253048625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2928298341886218168699083 4392447512829327253048625)
      ·
        refine ⟨3294335634621995439786469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4392447512829327253048625 3294335634621995439786469)
        ·
          refine ⟨617687931491624144959963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3294335634621995439786469 617687931491624144959963)
          ·
            refine ⟨926531897237436217439945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617687931491624144959963 926531897237436217439945)
            ·
              refine ⟨694898922928077163079959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 926531897237436217439945 694898922928077163079959)
              ·
                refine ⟨1042348384392115744619939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 694898922928077163079959 1042348384392115744619939)
                ·
                  refine ⟨1563522576588173616929909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1042348384392115744619939 1563522576588173616929909)
                  ·
                    refine ⟨146580241555141276587179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1563522576588173616929909 146580241555141276587179)
                    ·
                      rfl

theorem cell22_428196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_428196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_428196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_428196 prefixEnd_428196 := by exact prefixLift 428196
  have htrace : WordTrace (prefixWord ++ tailWord_428196) baseStart_428196 baseEnd_428196 := by
    simpa [prefixWord, tailWord_428196, baseEnd_428196] using wordTrace_append hprefix tailTrace_428196
  have hstable : (prefixWord ++ tailWord_428196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428196).length < 2 ^ (prefixWord ++ tailWord_428196).sum := by decide
  have hdescent : baseEnd_428196 < baseStart_428196 := by decide
  rcases family_descends (prefixWord ++ tailWord_428196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428292 : List Nat := [2, 3, 2, 2, 3, 1, 3, 2, 1, 3]
def baseStart_428292 : Nat := 118140960795 + 428292 * 2 ^ 59
def prefixEnd_428292 : Nat := 4983230072969 + 3 ^ 40 * 428292 * 2
def baseEnd_428292 : Nat := 146613104317029026186885

theorem tailTrace_428292 : CollatzResearch.WordTrace tailWord_428292 prefixEnd_428292 146613104317029026186885 := by
  unfold tailWord_428292
  simp only [CollatzResearch.WordTrace]
  refine ⟨7810546282189352647611565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10414061709585803530148753 7810546282189352647611565)
  ·
    refine ⟨2928954855821007242854337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7810546282189352647611565 2928954855821007242854337)
    ·
      refine ⟨2196716141865755432140753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2928954855821007242854337 2196716141865755432140753)
      ·
        refine ⟨1647537106399316574105565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2196716141865755432140753 1647537106399316574105565)
        ·
          refine ⟨617826414899743715289587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1647537106399316574105565 617826414899743715289587)
          ·
            refine ⟨926739622349615572934381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617826414899743715289587 926739622349615572934381)
            ·
              refine ⟨347527358381105839850393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 926739622349615572934381 347527358381105839850393)
              ·
                refine ⟨260645518785829379887795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 347527358381105839850393 260645518785829379887795)
                ·
                  refine ⟨390968278178744069831693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 260645518785829379887795 390968278178744069831693)
                  ·
                    refine ⟨146613104317029026186885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 390968278178744069831693 146613104317029026186885)
                    ·
                      rfl

theorem cell22_428292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_428292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_428292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_428292 prefixEnd_428292 := by exact prefixLift 428292
  have htrace : WordTrace (prefixWord ++ tailWord_428292) baseStart_428292 baseEnd_428292 := by
    simpa [prefixWord, tailWord_428292, baseEnd_428292] using wordTrace_append hprefix tailTrace_428292
  have hstable : (prefixWord ++ tailWord_428292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428292).length < 2 ^ (prefixWord ++ tailWord_428292).sum := by decide
  have hdescent : baseEnd_428292 < baseStart_428292 := by decide
  rcases family_descends (prefixWord ++ tailWord_428292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428346 : List Nat := [3, 1, 1, 1, 4, 2, 2, 2, 2, 4]
def baseStart_428346 : Nat := 118140960795 + 428346 * 2 ^ 59
def prefixEnd_428346 : Nat := 4983230072969 + 3 ^ 40 * 428346 * 2
def baseEnd_428346 : Nat := 146631589620590885336719

theorem tailTrace_428346 : CollatzResearch.WordTrace tailWord_428346 prefixEnd_428346 146631589620590885336719 := by
  unfold tailWord_428346
  simp only [CollatzResearch.WordTrace]
  refine ⟨3905765526545768129422223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10415374737455381678459261 3905765526545768129422223)
  ·
    refine ⟨5858648289818652194133335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3905765526545768129422223 5858648289818652194133335)
    ·
      refine ⟨8787972434727978291200003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5858648289818652194133335 8787972434727978291200003)
      ·
        refine ⟨13181958652091967436800005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8787972434727978291200003 13181958652091967436800005)
        ·
          refine ⟨2471617247267243894400001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13181958652091967436800005 2471617247267243894400001)
          ·
            refine ⟨1853712935450432920800001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2471617247267243894400001 1853712935450432920800001)
            ·
              refine ⟨1390284701587824690600001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1853712935450432920800001 1390284701587824690600001)
              ·
                refine ⟨1042713526190868517950001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1390284701587824690600001 1042713526190868517950001)
                ·
                  refine ⟨782035144643151388462501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1042713526190868517950001 782035144643151388462501)
                  ·
                    refine ⟨146631589620590885336719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 782035144643151388462501 146631589620590885336719)
                    ·
                      rfl

theorem cell22_428346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_428346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_428346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_428346 prefixEnd_428346 := by exact prefixLift 428346
  have htrace : WordTrace (prefixWord ++ tailWord_428346) baseStart_428346 baseEnd_428346 := by
    simpa [prefixWord, tailWord_428346, baseEnd_428346] using wordTrace_append hprefix tailTrace_428346
  have hstable : (prefixWord ++ tailWord_428346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428346).length < 2 ^ (prefixWord ++ tailWord_428346).sum := by decide
  have hdescent : baseEnd_428346 < baseStart_428346 := by decide
  rcases family_descends (prefixWord ++ tailWord_428346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428348 : List Nat := [2, 2, 2, 2, 1, 2, 4, 2, 2, 3]
def baseStart_428348 : Nat := 118140960795 + 428348 * 2 ^ 59
def prefixEnd_428348 : Nat := 4983230072969 + 3 ^ 40 * 428348 * 2
def baseEnd_428348 : Nat := 146632274261463546786713

theorem tailTrace_428348 : CollatzResearch.WordTrace tailWord_428348 prefixEnd_428348 146632274261463546786713 := by
  unfold tailWord_428348
  simp only [CollatzResearch.WordTrace]
  refine ⟨7811567526087913429630849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10415423368117217906174465 7811567526087913429630849)
  ·
    refine ⟨5858675644565935072223137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7811567526087913429630849 5858675644565935072223137)
    ·
      refine ⟨4394006733424451304167353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5858675644565935072223137 4394006733424451304167353)
      ·
        refine ⟨3295505050068338478125515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4394006733424451304167353 3295505050068338478125515)
        ·
          refine ⟨4943257575102507717188273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3295505050068338478125515 4943257575102507717188273)
          ·
            refine ⟨3707443181326880787891205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4943257575102507717188273 3707443181326880787891205)
            ·
              refine ⟨695145596498790147729601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3707443181326880787891205 695145596498790147729601)
              ·
                refine ⟨521359197374092610797201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 695145596498790147729601 521359197374092610797201)
                ·
                  refine ⟨391019398030569458097901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 521359197374092610797201 391019398030569458097901)
                  ·
                    refine ⟨146632274261463546786713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 391019398030569458097901 146632274261463546786713)
                    ·
                      rfl

theorem cell22_428348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_428348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_428348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_428348 prefixEnd_428348 := by exact prefixLift 428348
  have htrace : WordTrace (prefixWord ++ tailWord_428348) baseStart_428348 baseEnd_428348 := by
    simpa [prefixWord, tailWord_428348, baseEnd_428348] using wordTrace_append hprefix tailTrace_428348
  have hstable : (prefixWord ++ tailWord_428348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428348).length < 2 ^ (prefixWord ++ tailWord_428348).sum := by decide
  have hdescent : baseEnd_428348 < baseStart_428348 := by decide
  rcases family_descends (prefixWord ++ tailWord_428348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428350 : List Nat := [4, 2, 1, 2, 1, 2, 4, 2, 4]
def baseStart_428350 : Nat := 118140960795 + 428350 * 2 ^ 59
def prefixEnd_428350 : Nat := 4983230072969 + 3 ^ 40 * 428350 * 2
def baseEnd_428350 : Nat := 48877652967445402745569

theorem tailTrace_428350 : CollatzResearch.WordTrace tailWord_428350 prefixEnd_428350 48877652967445402745569 := by
  unfold tailWord_428350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1952900999771072650104313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10415471998779054133889669 1952900999771072650104313)
  ·
    refine ⟨1464675749828304487578235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1952900999771072650104313 1464675749828304487578235)
    ·
      refine ⟨2197013624742456731367353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1464675749828304487578235 2197013624742456731367353)
      ·
        refine ⟨1647760218556842548525515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2197013624742456731367353 1647760218556842548525515)
        ·
          refine ⟨2471640327835263822788273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1647760218556842548525515 2471640327835263822788273)
          ·
            refine ⟨1853730245876447867091205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2471640327835263822788273 1853730245876447867091205)
            ·
              refine ⟨347574421101833975079601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1853730245876447867091205 347574421101833975079601)
              ·
                refine ⟨260680815826375481309701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 347574421101833975079601 260680815826375481309701)
                ·
                  refine ⟨48877652967445402745569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 260680815826375481309701 48877652967445402745569)
                  ·
                    rfl

theorem cell22_428350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_428350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_428350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_428350 prefixEnd_428350 := by exact prefixLift 428350
  have htrace : WordTrace (prefixWord ++ tailWord_428350) baseStart_428350 baseEnd_428350 := by
    simpa [prefixWord, tailWord_428350, baseEnd_428350] using wordTrace_append hprefix tailTrace_428350
  have hstable : (prefixWord ++ tailWord_428350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428350).length < 2 ^ (prefixWord ++ tailWord_428350).sum := by decide
  have hdescent : baseEnd_428350 < baseStart_428350 := by decide
  rcases family_descends (prefixWord ++ tailWord_428350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428423 : List Nat := [1, 1, 4, 2, 2, 1, 5, 1, 5]
def baseStart_428423 : Nat := 118140960795 + 428423 * 2 ^ 59
def prefixEnd_428423 : Nat := 4983230072969 + 3 ^ 40 * 428423 * 2
def baseEnd_428423 : Nat := 48885982764729450387161

theorem tailTrace_428423 : CollatzResearch.WordTrace tailWord_428423 prefixEnd_428423 48885982764729450387161 := by
  unfold tailWord_428423
  simp only [CollatzResearch.WordTrace]
  refine ⟨15625870526904114668241923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10417247017936076445494615 15625870526904114668241923)
  ·
    refine ⟨23438805790356172002362885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15625870526904114668241923 23438805790356172002362885)
    ·
      refine ⟨4394776085691782250443041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23438805790356172002362885 4394776085691782250443041)
      ·
        refine ⟨3296082064268836687832281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4394776085691782250443041 3296082064268836687832281)
        ·
          refine ⟨2472061548201627515874211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3296082064268836687832281 2472061548201627515874211)
          ·
            refine ⟨3708092322302441273811317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2472061548201627515874211 3708092322302441273811317)
            ·
              refine ⟨347633655215853869419811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3708092322302441273811317 347633655215853869419811)
              ·
                refine ⟨521450482823780804129717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 347633655215853869419811 521450482823780804129717)
                ·
                  refine ⟨48885982764729450387161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 521450482823780804129717 48885982764729450387161)
                  ·
                    rfl

theorem cell22_428423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 5].length) (baseStart_428423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_428423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_428423 prefixEnd_428423 := by exact prefixLift 428423
  have htrace : WordTrace (prefixWord ++ tailWord_428423) baseStart_428423 baseEnd_428423 := by
    simpa [prefixWord, tailWord_428423, baseEnd_428423] using wordTrace_append hprefix tailTrace_428423
  have hstable : (prefixWord ++ tailWord_428423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428423).length < 2 ^ (prefixWord ++ tailWord_428423).sum := by decide
  have hdescent : baseEnd_428423 < baseStart_428423 := by decide
  rcases family_descends (prefixWord ++ tailWord_428423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428517 : List Nat := [1, 3, 1, 5, 2, 1, 2, 2, 2, 3]
def baseStart_428517 : Nat := 118140960795 + 428517 * 2 ^ 59
def prefixEnd_428517 : Nat := 4983230072969 + 3 ^ 40 * 428517 * 2
def baseEnd_428517 : Nat := 146690126415203439311195

theorem tailTrace_428517 : CollatzResearch.WordTrace tailWord_428517 prefixEnd_428517 146690126415203439311195 := by
  unfold tailWord_428517
  simp only [CollatzResearch.WordTrace]
  refine ⟨15629298988563568722163805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10419532659042379148109203 15629298988563568722163805)
  ·
    refine ⟨5860987120711338270811427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15629298988563568722163805 5860987120711338270811427)
    ·
      refine ⟨8791480681067007406217141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5860987120711338270811427 8791480681067007406217141)
      ·
        refine ⟨824201313850031944332857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8791480681067007406217141 824201313850031944332857)
        ·
          refine ⟨618150985387523958249643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 824201313850031944332857 618150985387523958249643)
          ·
            refine ⟨927226478081285937374465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618150985387523958249643 927226478081285937374465)
            ·
              refine ⟨695419858560964453030849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 927226478081285937374465 695419858560964453030849)
              ·
                refine ⟨521564893920723339773137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 695419858560964453030849 521564893920723339773137)
                ·
                  refine ⟨391173670440542504829853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 521564893920723339773137 391173670440542504829853)
                  ·
                    refine ⟨146690126415203439311195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 391173670440542504829853 146690126415203439311195)
                    ·
                      rfl

theorem cell22_428517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 2, 3].length) (baseStart_428517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_428517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_428517 prefixEnd_428517 := by exact prefixLift 428517
  have htrace : WordTrace (prefixWord ++ tailWord_428517) baseStart_428517 baseEnd_428517 := by
    simpa [prefixWord, tailWord_428517, baseEnd_428517] using wordTrace_append hprefix tailTrace_428517
  have hstable : (prefixWord ++ tailWord_428517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428517).length < 2 ^ (prefixWord ++ tailWord_428517).sum := by decide
  have hdescent : baseEnd_428517 < baseStart_428517 := by decide
  rcases family_descends (prefixWord ++ tailWord_428517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428528 : List Nat := [2, 1, 1, 1, 3, 3, 2, 3, 3, 3]
def baseStart_428528 : Nat := 118140960795 + 428528 * 2 ^ 59
def prefixEnd_428528 : Nat := 4983230072969 + 3 ^ 40 * 428528 * 2
def baseEnd_428528 : Nat := 146693891940003077286161

theorem tailTrace_428528 : CollatzResearch.WordTrace tailWord_428528 prefixEnd_428528 146693891940003077286161 := by
  unfold tailWord_428528
  simp only [CollatzResearch.WordTrace]
  refine ⟨7814850095761858800407119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10419800127682478400542825 7814850095761858800407119)
  ·
    refine ⟨11722275143642788200610679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7814850095761858800407119 11722275143642788200610679)
    ·
      refine ⟨17583412715464182300916019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11722275143642788200610679 17583412715464182300916019)
      ·
        refine ⟨26375119073196273451374029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17583412715464182300916019 26375119073196273451374029)
        ·
          refine ⟨9890669652448602544265261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26375119073196273451374029 9890669652448602544265261)
          ·
            refine ⟨3709001119668225954099473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9890669652448602544265261 3709001119668225954099473)
            ·
              refine ⟨2781750839751169465574605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3709001119668225954099473 2781750839751169465574605)
              ·
                refine ⟨1043156564906688549590477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2781750839751169465574605 1043156564906688549590477)
                ·
                  refine ⟨391183711840008206096429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1043156564906688549590477 391183711840008206096429)
                  ·
                    refine ⟨146693891940003077286161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 391183711840008206096429 146693891940003077286161)
                    ·
                      rfl

theorem cell22_428528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 3, 3].length) (baseStart_428528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_428528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_428528 prefixEnd_428528 := by exact prefixLift 428528
  have htrace : WordTrace (prefixWord ++ tailWord_428528) baseStart_428528 baseEnd_428528 := by
    simpa [prefixWord, tailWord_428528, baseEnd_428528] using wordTrace_append hprefix tailTrace_428528
  have hstable : (prefixWord ++ tailWord_428528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428528).length < 2 ^ (prefixWord ++ tailWord_428528).sum := by decide
  have hdescent : baseEnd_428528 < baseStart_428528 := by decide
  rcases family_descends (prefixWord ++ tailWord_428528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428530 : List Nat := [3, 2, 1, 4, 2, 2, 1, 7]
def baseStart_428530 : Nat := 118140960795 + 428530 * 2 ^ 59
def prefixEnd_428530 : Nat := 4983230072969 + 3 ^ 40 * 428530 * 2
def baseEnd_428530 : Nat := 16299397397875082081795

theorem tailTrace_428530 : CollatzResearch.WordTrace tailWord_428530 prefixEnd_428530 16299397397875082081795 := by
  unfold tailWord_428530
  simp only [CollatzResearch.WordTrace]
  refine ⟨3907443284379117985596761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10419848758344314628258029 3907443284379117985596761)
  ·
    refine ⟨2930582463284338489197571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3907443284379117985596761 2930582463284338489197571)
    ·
      refine ⟨4395873694926507733796357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2930582463284338489197571 4395873694926507733796357)
      ·
        refine ⟨824226317798720200086817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4395873694926507733796357 824226317798720200086817)
        ·
          refine ⟨618169738349040150065113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 824226317798720200086817 618169738349040150065113)
          ·
            refine ⟨463627303761780112548835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 618169738349040150065113 463627303761780112548835)
            ·
              refine ⟨695440955642670168823253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463627303761780112548835 695440955642670168823253)
              ·
                refine ⟨16299397397875082081795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 695440955642670168823253 16299397397875082081795)
                ·
                  rfl

theorem cell22_428530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 7].length) (baseStart_428530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_428530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_428530 prefixEnd_428530 := by exact prefixLift 428530
  have htrace : WordTrace (prefixWord ++ tailWord_428530) baseStart_428530 baseEnd_428530 := by
    simpa [prefixWord, tailWord_428530, baseEnd_428530] using wordTrace_append hprefix tailTrace_428530
  have hstable : (prefixWord ++ tailWord_428530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428530).length < 2 ^ (prefixWord ++ tailWord_428530).sum := by decide
  have hdescent : baseEnd_428530 < baseStart_428530 := by decide
  rcases family_descends (prefixWord ++ tailWord_428530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428545 : List Nat := [1, 2, 4, 1, 3, 2, 1, 2, 3, 3]
def baseStart_428545 : Nat := 118140960795 + 428545 * 2 ^ 59
def prefixEnd_428545 : Nat := 4983230072969 + 3 ^ 40 * 428545 * 2
def baseEnd_428545 : Nat := 146699711387420699611109

theorem tailTrace_428545 : CollatzResearch.WordTrace tailWord_428545 prefixEnd_428545 146699711387420699611109 := by
  unfold tailWord_428545
  simp only [CollatzResearch.WordTrace]
  refine ⟨15630320232462129504183089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10420213488308086336122059 15630320232462129504183089)
  ·
    refine ⟨11722740174346597128137317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15630320232462129504183089 11722740174346597128137317)
    ·
      refine ⟨2198013782689986961525747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11722740174346597128137317 2198013782689986961525747)
      ·
        refine ⟨3297020674034980442288621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2198013782689986961525747 3297020674034980442288621)
        ·
          refine ⟨1236382752763117665858233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3297020674034980442288621 1236382752763117665858233)
          ·
            refine ⟨927287064572338249393675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1236382752763117665858233 927287064572338249393675)
            ·
              refine ⟨1390930596858507374090513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 927287064572338249393675 1390930596858507374090513)
              ·
                refine ⟨1043197947643880530567885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1390930596858507374090513 1043197947643880530567885)
                ·
                  refine ⟨391199230366455198962957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1043197947643880530567885 391199230366455198962957)
                  ·
                    refine ⟨146699711387420699611109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 391199230366455198962957 146699711387420699611109)
                    ·
                      rfl

theorem cell22_428545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_428545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_428545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_428545 prefixEnd_428545 := by exact prefixLift 428545
  have htrace : WordTrace (prefixWord ++ tailWord_428545) baseStart_428545 baseEnd_428545 := by
    simpa [prefixWord, tailWord_428545, baseEnd_428545] using wordTrace_append hprefix tailTrace_428545
  have hstable : (prefixWord ++ tailWord_428545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428545).length < 2 ^ (prefixWord ++ tailWord_428545).sum := by decide
  have hdescent : baseEnd_428545 < baseStart_428545 := by decide
  rcases family_descends (prefixWord ++ tailWord_428545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428573 : List Nat := [1, 4, 2, 2, 1, 2, 1, 2, 2, 5]
def baseStart_428573 : Nat := 118140960795 + 428573 * 2 ^ 59
def prefixEnd_428573 : Nat := 4983230072969 + 3 ^ 40 * 428573 * 2
def baseEnd_428573 : Nat := 146709296359637959911023

theorem tailTrace_428573 : CollatzResearch.WordTrace tailWord_428573 prefixEnd_428573 146709296359637959911023 := by
  unfold tailWord_428573
  simp only [CollatzResearch.WordTrace]
  refine ⟨15631341476360690286202373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10420894317573793524134915 15631341476360690286202373)
  ·
    refine ⟨2930876526817629428662945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15631341476360690286202373 2930876526817629428662945)
    ·
      refine ⟨2198157395113222071497209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2930876526817629428662945 2198157395113222071497209)
      ·
        refine ⟨1648618046334916553622907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2198157395113222071497209 1648618046334916553622907)
        ·
          refine ⟨2472927069502374830434361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1648618046334916553622907 2472927069502374830434361)
          ·
            refine ⟨1854695302126781122825771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2472927069502374830434361 1854695302126781122825771)
            ·
              refine ⟨2782042953190171684238657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1854695302126781122825771 2782042953190171684238657)
              ·
                refine ⟨2086532214892628763178993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2782042953190171684238657 2086532214892628763178993)
                ·
                  refine ⟨1564899161169471572384245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2086532214892628763178993 1564899161169471572384245)
                  ·
                    refine ⟨146709296359637959911023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1564899161169471572384245 146709296359637959911023)
                    ·
                      rfl

theorem cell22_428573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_428573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_428573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_428573 prefixEnd_428573 := by exact prefixLift 428573
  have htrace : WordTrace (prefixWord ++ tailWord_428573) baseStart_428573 baseEnd_428573 := by
    simpa [prefixWord, tailWord_428573, baseEnd_428573] using wordTrace_append hprefix tailTrace_428573
  have hstable : (prefixWord ++ tailWord_428573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428573).length < 2 ^ (prefixWord ++ tailWord_428573).sum := by decide
  have hdescent : baseEnd_428573 < baseStart_428573 := by decide
  rcases family_descends (prefixWord ++ tailWord_428573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428605 : List Nat := [1, 4, 1, 3, 2, 1, 1, 4, 1, 4]
def baseStart_428605 : Nat := 118140960795 + 428605 * 2 ^ 59
def prefixEnd_428605 : Nat := 4983230072969 + 3 ^ 40 * 428605 * 2
def baseEnd_428605 : Nat := 146720250613600543110925

theorem tailTrace_428605 : CollatzResearch.WordTrace tailWord_428605 prefixEnd_428605 146720250613600543110925 := by
  unfold tailWord_428605
  simp only [CollatzResearch.WordTrace]
  refine ⟨15632508612244759751367269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10421672408163173167578179 15632508612244759751367269)
  ·
    refine ⟨2931095364795892453381363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15632508612244759751367269 2931095364795892453381363)
    ·
      refine ⟨4396643047193838680072045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2931095364795892453381363 4396643047193838680072045)
      ·
        refine ⟨1648741142697689505027017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4396643047193838680072045 1648741142697689505027017)
        ·
          refine ⟨1236555857023267128770263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1648741142697689505027017 1236555857023267128770263)
          ·
            refine ⟨1854833785534900693155395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1236555857023267128770263 1854833785534900693155395)
            ·
              refine ⟨2782250678302351039733093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1854833785534900693155395 2782250678302351039733093)
              ·
                refine ⟨521672002181690819949955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2782250678302351039733093 521672002181690819949955)
                ·
                  refine ⟨782508003272536229924933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 521672002181690819949955 782508003272536229924933)
                  ·
                    refine ⟨146720250613600543110925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 782508003272536229924933 146720250613600543110925)
                    ·
                      rfl

theorem cell22_428605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_428605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_428605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_428605 prefixEnd_428605 := by exact prefixLift 428605
  have htrace : WordTrace (prefixWord ++ tailWord_428605) baseStart_428605 baseEnd_428605 := by
    simpa [prefixWord, tailWord_428605, baseEnd_428605] using wordTrace_append hprefix tailTrace_428605
  have hstable : (prefixWord ++ tailWord_428605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428605).length < 2 ^ (prefixWord ++ tailWord_428605).sum := by decide
  have hdescent : baseEnd_428605 < baseStart_428605 := by decide
  rcases family_descends (prefixWord ++ tailWord_428605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428652 : List Nat := [2, 2, 1, 1, 3, 1, 6, 1, 2, 3]
def baseStart_428652 : Nat := 118140960795 + 428652 * 2 ^ 59
def prefixEnd_428652 : Nat := 4983230072969 + 3 ^ 40 * 428652 * 2
def baseEnd_428652 : Nat := 146736339674108087185781

theorem tailTrace_428652 : CollatzResearch.WordTrace tailWord_428652 prefixEnd_428652 146736339674108087185781 := by
  unfold tailWord_428652
  simp only [CollatzResearch.WordTrace]
  refine ⟨7817111421537243389164105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10422815228716324518885473 7817111421537243389164105)
  ·
    refine ⟨5862833566152932541873079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7817111421537243389164105 5862833566152932541873079)
    ·
      refine ⟨8794250349229398812809619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5862833566152932541873079 8794250349229398812809619)
      ·
        refine ⟨13191375523844098219214429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8794250349229398812809619 13191375523844098219214429)
        ·
          refine ⟨4946765821441536832205411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13191375523844098219214429 4946765821441536832205411)
          ·
            refine ⟨7420148732162305248308117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4946765821441536832205411 7420148732162305248308117)
            ·
              refine ⟨347819471820108058514443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7420148732162305248308117 347819471820108058514443)
              ·
                refine ⟨521729207730162087771665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 347819471820108058514443 521729207730162087771665)
                ·
                  refine ⟨391296905797621565828749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 521729207730162087771665 391296905797621565828749)
                  ·
                    refine ⟨146736339674108087185781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 391296905797621565828749 146736339674108087185781)
                    ·
                      rfl

theorem cell22_428652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 3].length) (baseStart_428652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_428652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_428652 prefixEnd_428652 := by exact prefixLift 428652
  have htrace : WordTrace (prefixWord ++ tailWord_428652) baseStart_428652 baseEnd_428652 := by
    simpa [prefixWord, tailWord_428652, baseEnd_428652] using wordTrace_append hprefix tailTrace_428652
  have hstable : (prefixWord ++ tailWord_428652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428652).length < 2 ^ (prefixWord ++ tailWord_428652).sum := by decide
  have hdescent : baseEnd_428652 < baseStart_428652 := by decide
  rcases family_descends (prefixWord ++ tailWord_428652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428697 : List Nat := [1, 2, 1, 2, 1, 2, 5, 4, 1, 3]
def baseStart_428697 : Nat := 118140960795 + 428697 * 2 ^ 59
def prefixEnd_428697 : Nat := 4983230072969 + 3 ^ 40 * 428697 * 2
def baseEnd_428697 : Nat := 146751744093742969810643

theorem tailTrace_428697 : CollatzResearch.WordTrace tailWord_428697 prefixEnd_428697 146751744093742969810643 := by
  unfold tailWord_428697
  simp only [CollatzResearch.WordTrace]
  refine ⟨15635864127911459463716345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10423909418607639642477563 15635864127911459463716345)
  ·
    refine ⟨11726898095933594597787259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15635864127911459463716345 11726898095933594597787259)
    ·
      refine ⟨17590347143900391896680889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11726898095933594597787259 17590347143900391896680889)
      ·
        refine ⟨13192760357925293922510667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17590347143900391896680889 13192760357925293922510667)
        ·
          refine ⟨19789140536887940883766001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13192760357925293922510667 19789140536887940883766001)
          ·
            refine ⟨14841855402665955662824501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19789140536887940883766001 14841855402665955662824501)
            ·
              refine ⟨1391423943999933343389797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14841855402665955662824501 1391423943999933343389797)
              ·
                refine ⟨260891989499987501885587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1391423943999933343389797 260891989499987501885587)
                ·
                  refine ⟨391337984249981252828381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 260891989499987501885587 391337984249981252828381)
                  ·
                    refine ⟨146751744093742969810643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 391337984249981252828381 146751744093742969810643)
                    ·
                      rfl

theorem cell22_428697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 4, 1, 3].length) (baseStart_428697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_428697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_428697 prefixEnd_428697 := by exact prefixLift 428697
  have htrace : WordTrace (prefixWord ++ tailWord_428697) baseStart_428697 baseEnd_428697 := by
    simpa [prefixWord, tailWord_428697, baseEnd_428697] using wordTrace_append hprefix tailTrace_428697
  have hstable : (prefixWord ++ tailWord_428697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428697).length < 2 ^ (prefixWord ++ tailWord_428697).sum := by decide
  have hdescent : baseEnd_428697 < baseStart_428697 := by decide
  rcases family_descends (prefixWord ++ tailWord_428697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428785 : List Nat := [1, 2, 2, 2, 2, 2, 2, 3, 2, 4]
def baseStart_428785 : Nat := 118140960795 + 428785 * 2 ^ 59
def prefixEnd_428785 : Nat := 4983230072969 + 3 ^ 40 * 428785 * 2
def baseEnd_428785 : Nat := 146781868292140073610373

theorem tailTrace_428785 : CollatzResearch.WordTrace tailWord_428785 prefixEnd_428785 146781868292140073610373 := by
  unfold tailWord_428785
  simp only [CollatzResearch.WordTrace]
  refine ⟨15639073751592650492919809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10426049167728433661946539 15639073751592650492919809)
  ·
    refine ⟨11729305313694487869689857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15639073751592650492919809 11729305313694487869689857)
    ·
      refine ⟨8796978985270865902267393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11729305313694487869689857 8796978985270865902267393)
      ·
        refine ⟨6597734238953149426700545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8796978985270865902267393 6597734238953149426700545)
        ·
          refine ⟨4948300679214862070025409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6597734238953149426700545 4948300679214862070025409)
          ·
            refine ⟨3711225509411146552519057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4948300679214862070025409 3711225509411146552519057)
            ·
              refine ⟨2783419132058359914389293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3711225509411146552519057 2783419132058359914389293)
              ·
                refine ⟨1043782174521884967895985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2783419132058359914389293 1043782174521884967895985)
                ·
                  refine ⟨782836630891413725921989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1043782174521884967895985 782836630891413725921989)
                  ·
                    refine ⟨146781868292140073610373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 782836630891413725921989 146781868292140073610373)
                    ·
                      rfl

theorem cell22_428785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_428785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_428785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_428785 prefixEnd_428785 := by exact prefixLift 428785
  have htrace : WordTrace (prefixWord ++ tailWord_428785) baseStart_428785 baseEnd_428785 := by
    simpa [prefixWord, tailWord_428785, baseEnd_428785] using wordTrace_append hprefix tailTrace_428785
  have hstable : (prefixWord ++ tailWord_428785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428785).length < 2 ^ (prefixWord ++ tailWord_428785).sum := by decide
  have hdescent : baseEnd_428785 < baseStart_428785 := by decide
  rcases family_descends (prefixWord ++ tailWord_428785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428802 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_428802 : Nat := 118140960795 + 428802 * 2 ^ 59
def prefixEnd_428802 : Nat := 4983230072969 + 3 ^ 40 * 428802 * 2
def baseEnd_428802 : Nat := 146787687739557695935321

theorem tailTrace_428802 : CollatzResearch.WordTrace tailWord_428802 prefixEnd_428802 146787687739557695935321 := by
  unfold tailWord_428802
  simp only [CollatzResearch.WordTrace]
  refine ⟨3909923448132765599072165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10426462528354041597525773 3909923448132765599072165)
  ·
    refine ⟨733110646524893549826031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3909923448132765599072165 733110646524893549826031)
    ·
      refine ⟨1099665969787340324739047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 733110646524893549826031 1099665969787340324739047)
      ·
        refine ⟨1649498954681010487108571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1099665969787340324739047 1649498954681010487108571)
        ·
          refine ⟨2474248432021515730662857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1649498954681010487108571 2474248432021515730662857)
          ·
            refine ⟨1855686324016136797997143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2474248432021515730662857 1855686324016136797997143)
            ·
              refine ⟨2783529486024205196995715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1855686324016136797997143 2783529486024205196995715)
              ·
                refine ⟨4175294229036307795493573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2783529486024205196995715 4175294229036307795493573)
                ·
                  refine ⟨782867667944307711655045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4175294229036307795493573 782867667944307711655045)
                  ·
                    refine ⟨146787687739557695935321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 782867667944307711655045 146787687739557695935321)
                    ·
                      rfl

theorem cell22_428802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_428802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_428802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_428802 prefixEnd_428802 := by exact prefixLift 428802
  have htrace : WordTrace (prefixWord ++ tailWord_428802) baseStart_428802 baseEnd_428802 := by
    simpa [prefixWord, tailWord_428802, baseEnd_428802] using wordTrace_append hprefix tailTrace_428802
  have hstable : (prefixWord ++ tailWord_428802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428802).length < 2 ^ (prefixWord ++ tailWord_428802).sum := by decide
  have hdescent : baseEnd_428802 < baseStart_428802 := by decide
  rcases family_descends (prefixWord ++ tailWord_428802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428849 : List Nat := [1, 2, 2, 3, 2, 1, 2, 5, 1, 3]
def baseStart_428849 : Nat := 118140960795 + 428849 * 2 ^ 59
def prefixEnd_428849 : Nat := 4983230072969 + 3 ^ 40 * 428849 * 2
def baseEnd_428849 : Nat := 146803776800065240010177

theorem tailTrace_428849 : CollatzResearch.WordTrace tailWord_428849 prefixEnd_428849 146803776800065240010177 := by
  unfold tailWord_428849
  simp only [CollatzResearch.WordTrace]
  refine ⟨15641408023360789423249601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10427605348907192948833067 15641408023360789423249601)
  ·
    refine ⟨11731056017520592067437201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15641408023360789423249601 11731056017520592067437201)
    ·
      refine ⟨8798292013140444050577901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11731056017520592067437201 8798292013140444050577901)
      ·
        refine ⟨3299359504927666518966713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8798292013140444050577901 3299359504927666518966713)
        ·
          refine ⟨2474519628695749889225035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3299359504927666518966713 2474519628695749889225035)
          ·
            refine ⟨3711779443043624833837553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2474519628695749889225035 3711779443043624833837553)
            ·
              refine ⟨2783834582282718625378165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3711779443043624833837553 2783834582282718625378165)
              ·
                refine ⟨260984492089004871129203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2783834582282718625378165 260984492089004871129203)
                ·
                  refine ⟨391476738133507306693805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 260984492089004871129203 391476738133507306693805)
                  ·
                    refine ⟨146803776800065240010177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 391476738133507306693805 146803776800065240010177)
                    ·
                      rfl

theorem cell22_428849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 5, 1, 3].length) (baseStart_428849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_428849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_428849 prefixEnd_428849 := by exact prefixLift 428849
  have htrace : WordTrace (prefixWord ++ tailWord_428849) baseStart_428849 baseEnd_428849 := by
    simpa [prefixWord, tailWord_428849, baseEnd_428849] using wordTrace_append hprefix tailTrace_428849
  have hstable : (prefixWord ++ tailWord_428849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428849).length < 2 ^ (prefixWord ++ tailWord_428849).sum := by decide
  have hdescent : baseEnd_428849 < baseStart_428849 := by decide
  rcases family_descends (prefixWord ++ tailWord_428849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428860 : List Nat := [2, 2, 2, 2, 1, 1, 1, 4, 2, 5]
def baseStart_428860 : Nat := 118140960795 + 428860 * 2 ^ 59
def prefixEnd_428860 : Nat := 4983230072969 + 3 ^ 40 * 428860 * 2
def baseEnd_428860 : Nat := 146807542324864877985143

theorem tailTrace_428860 : CollatzResearch.WordTrace tailWord_428860 prefixEnd_428860 146807542324864877985143 := by
  unfold tailWord_428860
  simp only [CollatzResearch.WordTrace]
  refine ⟨7820904613160469150950017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10427872817547292201266689 7820904613160469150950017)
  ·
    refine ⟨5865678459870351863212513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7820904613160469150950017 5865678459870351863212513)
    ·
      refine ⟨4399258844902763897409385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5865678459870351863212513 4399258844902763897409385)
      ·
        refine ⟨3299444133677072923057039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4399258844902763897409385 3299444133677072923057039)
        ·
          refine ⟨4949166200515609384585559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3299444133677072923057039 4949166200515609384585559)
          ·
            refine ⟨7423749300773414076878339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4949166200515609384585559 7423749300773414076878339)
            ·
              refine ⟨11135623951160121115317509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7423749300773414076878339 11135623951160121115317509)
              ·
                refine ⟨2087929490842522709122033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11135623951160121115317509 2087929490842522709122033)
                ·
                  refine ⟨1565947118131892031841525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2087929490842522709122033 1565947118131892031841525)
                  ·
                    refine ⟨146807542324864877985143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1565947118131892031841525 146807542324864877985143)
                    ·
                      rfl

theorem cell22_428860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_428860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_428860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_428860 prefixEnd_428860 := by exact prefixLift 428860
  have htrace : WordTrace (prefixWord ++ tailWord_428860) baseStart_428860 baseEnd_428860 := by
    simpa [prefixWord, tailWord_428860, baseEnd_428860] using wordTrace_append hprefix tailTrace_428860
  have hstable : (prefixWord ++ tailWord_428860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428860).length < 2 ^ (prefixWord ++ tailWord_428860).sum := by decide
  have hdescent : baseEnd_428860 < baseStart_428860 := by decide
  rcases family_descends (prefixWord ++ tailWord_428860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428890 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 8]
def baseStart_428890 : Nat := 118140960795 + 428890 * 2 ^ 59
def prefixEnd_428890 : Nat := 4983230072969 + 3 ^ 40 * 428890 * 2
def baseEnd_428890 : Nat := 48939270645984933245017

theorem tailTrace_428890 : CollatzResearch.WordTrace tailWord_428890 prefixEnd_428890 48939270645984933245017 := by
  unfold tailWord_428890
  simp only [CollatzResearch.WordTrace]
  refine ⟨3910725854053063356373031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10428602277474835616994749 3910725854053063356373031)
  ·
    refine ⟨5866088781079595034559547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3910725854053063356373031 5866088781079595034559547)
    ·
      refine ⟨8799133171619392551839321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5866088781079595034559547 8799133171619392551839321)
      ·
        refine ⟨6599349878714544413879491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8799133171619392551839321 6599349878714544413879491)
        ·
          refine ⟨9899024818071816620819237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6599349878714544413879491 9899024818071816620819237)
          ·
            refine ⟨1856067153388465616403607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9899024818071816620819237 1856067153388465616403607)
            ·
              refine ⟨2784100730082698424605411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1856067153388465616403607 2784100730082698424605411)
              ·
                refine ⟨4176151095124047636908117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2784100730082698424605411 4176151095124047636908117)
                ·
                  refine ⟨48939270645984933245017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4176151095124047636908117 48939270645984933245017)
                  ·
                    rfl

theorem cell22_428890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 8].length) (baseStart_428890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_428890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_428890 prefixEnd_428890 := by exact prefixLift 428890
  have htrace : WordTrace (prefixWord ++ tailWord_428890) baseStart_428890 baseEnd_428890 := by
    simpa [prefixWord, tailWord_428890, baseEnd_428890] using wordTrace_append hprefix tailTrace_428890
  have hstable : (prefixWord ++ tailWord_428890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428890).length < 2 ^ (prefixWord ++ tailWord_428890).sum := by decide
  have hdescent : baseEnd_428890 < baseStart_428890 := by decide
  rcases family_descends (prefixWord ++ tailWord_428890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428907 : List Nat := [1, 1, 1, 1, 2, 2, 5, 5, 4]
def baseStart_428907 : Nat := 118140960795 + 428907 * 2 ^ 59
def prefixEnd_428907 : Nat := 4983230072969 + 3 ^ 40 * 428907 * 2
def baseEnd_428907 : Nat := 48941210461790807353333

theorem tailTrace_428907 : CollatzResearch.WordTrace tailWord_428907 prefixEnd_428907 48941210461790807353333 := by
  unfold tailWord_428907
  simp only [CollatzResearch.WordTrace]
  refine ⟨15643523457150665328860975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10429015638100443552573983 15643523457150665328860975)
  ·
    refine ⟨23465285185725997993291463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15643523457150665328860975 23465285185725997993291463)
    ·
      refine ⟨35197927778588996989937195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23465285185725997993291463 35197927778588996989937195)
      ·
        refine ⟨52796891667883495484905793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35197927778588996989937195 52796891667883495484905793)
        ·
          refine ⟨39597668750912621613679345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52796891667883495484905793 39597668750912621613679345)
          ·
            refine ⟨29698251563184466210259509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39597668750912621613679345 29698251563184466210259509)
            ·
              refine ⟨2784211084048543707211829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29698251563184466210259509 2784211084048543707211829)
              ·
                refine ⟨261019789129550972551109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2784211084048543707211829 261019789129550972551109)
                ·
                  refine ⟨48941210461790807353333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 261019789129550972551109 48941210461790807353333)
                  ·
                    rfl

theorem cell22_428907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5, 4].length) (baseStart_428907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_428907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_428907 prefixEnd_428907 := by exact prefixLift 428907
  have htrace : WordTrace (prefixWord ++ tailWord_428907) baseStart_428907 baseEnd_428907 := by
    simpa [prefixWord, tailWord_428907, baseEnd_428907] using wordTrace_append hprefix tailTrace_428907
  have hstable : (prefixWord ++ tailWord_428907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428907).length < 2 ^ (prefixWord ++ tailWord_428907).sum := by decide
  have hdescent : baseEnd_428907 < baseStart_428907 := by decide
  rcases family_descends (prefixWord ++ tailWord_428907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428965 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 3, 8]
def baseStart_428965 : Nat := 118140960795 + 428965 * 2 ^ 59
def prefixEnd_428965 : Nat := 4983230072969 + 3 ^ 40 * 428965 * 2
def baseEnd_428965 : Nat := 146843485970679604109821

theorem tailTrace_428965 : CollatzResearch.WordTrace tailWord_428965 prefixEnd_428965 146843485970679604109821 := by
  unfold tailWord_428965
  simp only [CollatzResearch.WordTrace]
  refine ⟨15645638890940541234472349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10430425927293694156314899 15645638890940541234472349)
  ·
    refine ⟨5867114584102702962927131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15645638890940541234472349 5867114584102702962927131)
    ·
      refine ⟨8800671876154054444390697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5867114584102702962927131 8800671876154054444390697)
      ·
        refine ⟨6600503907115540833293023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8800671876154054444390697 6600503907115540833293023)
        ·
          refine ⟨9900755860673311249939535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6600503907115540833293023 9900755860673311249939535)
          ·
            refine ⟨14851133791009966874909303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9900755860673311249939535 14851133791009966874909303)
            ·
              refine ⟨22276700686514950312363955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14851133791009966874909303 22276700686514950312363955)
              ·
                refine ⟨33415051029772425468545933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22276700686514950312363955 33415051029772425468545933)
                ·
                  refine ⟨12530644136164659550704725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33415051029772425468545933 12530644136164659550704725)
                  ·
                    refine ⟨146843485970679604109821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12530644136164659550704725 146843485970679604109821)
                    ·
                      rfl

theorem cell22_428965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_428965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_428965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_428965 prefixEnd_428965 := by exact prefixLift 428965
  have htrace : WordTrace (prefixWord ++ tailWord_428965) baseStart_428965 baseEnd_428965 := by
    simpa [prefixWord, tailWord_428965, baseEnd_428965] using wordTrace_append hprefix tailTrace_428965
  have hstable : (prefixWord ++ tailWord_428965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428965).length < 2 ^ (prefixWord ++ tailWord_428965).sum := by decide
  have hdescent : baseEnd_428965 < baseStart_428965 := by decide
  rcases family_descends (prefixWord ++ tailWord_428965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_428984 : List Nat := [2, 1, 2, 1, 2, 4, 3, 1, 3, 3]
def baseStart_428984 : Nat := 118140960795 + 428984 * 2 ^ 59
def prefixEnd_428984 : Nat := 4983230072969 + 3 ^ 40 * 428984 * 2
def baseEnd_428984 : Nat := 146849990058969887884763

theorem tailTrace_428984 : CollatzResearch.WordTrace tailWord_428984 prefixEnd_428984 146849990058969887884763 := by
  unfold tailWord_428984
  simp only [CollatzResearch.WordTrace]
  refine ⟨7823165938935853739707003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10430887918581138319609337 7823165938935853739707003)
  ·
    refine ⟨11734748908403780609560505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7823165938935853739707003 11734748908403780609560505)
    ·
      refine ⟨8801061681302835457170379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11734748908403780609560505 8801061681302835457170379)
      ·
        refine ⟨13201592521954253185755569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8801061681302835457170379 13201592521954253185755569)
        ·
          refine ⟨9901194391465689889316677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13201592521954253185755569 9901194391465689889316677)
          ·
            refine ⟨1856473948399816854246877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9901194391465689889316677 1856473948399816854246877)
            ·
              refine ⟨696177730649931320342579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1856473948399816854246877 696177730649931320342579)
              ·
                refine ⟨1044266595974896980513869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 696177730649931320342579 1044266595974896980513869)
                ·
                  refine ⟨391599973490586367692701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1044266595974896980513869 391599973490586367692701)
                  ·
                    refine ⟨146849990058969887884763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 391599973490586367692701 146849990058969887884763)
                    ·
                      rfl

theorem cell22_428984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 3, 3].length) (baseStart_428984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_428984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_428984 prefixEnd_428984 := by exact prefixLift 428984
  have htrace : WordTrace (prefixWord ++ tailWord_428984) baseStart_428984 baseEnd_428984 := by
    simpa [prefixWord, tailWord_428984, baseEnd_428984] using wordTrace_append hprefix tailTrace_428984
  have hstable : (prefixWord ++ tailWord_428984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_428984).length < 2 ^ (prefixWord ++ tailWord_428984).sum := by decide
  have hdescent : baseEnd_428984 < baseStart_428984 := by decide
  rcases family_descends (prefixWord ++ tailWord_428984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429005 : List Nat := [1, 6, 3, 1, 1, 1, 2, 1, 2, 4]
def baseStart_429005 : Nat := 118140960795 + 429005 * 2 ^ 59
def prefixEnd_429005 : Nat := 4983230072969 + 3 ^ 40 * 429005 * 2
def baseEnd_429005 : Nat := 146857178788132833109699

theorem tailTrace_429005 : CollatzResearch.WordTrace tailWord_429005 prefixEnd_429005 146857178788132833109699 := by
  unfold tailWord_429005
  simp only [CollatzResearch.WordTrace]
  refine ⟨15647097810795628065928469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10431398540530418710618979 15647097810795628065928469)
  ·
    refine ⟨733457709881045065590397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15647097810795628065928469 733457709881045065590397)
    ·
      refine ⟨275046641205391899596399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 733457709881045065590397 275046641205391899596399)
      ·
        refine ⟨412569961808087849394599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275046641205391899596399 412569961808087849394599)
        ·
          refine ⟨618854942712131774091899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412569961808087849394599 618854942712131774091899)
          ·
            refine ⟨928282414068197661137849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618854942712131774091899 928282414068197661137849)
            ·
              refine ⟨696211810551148245853387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 928282414068197661137849 696211810551148245853387)
              ·
                refine ⟨1044317715826722368780081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 696211810551148245853387 1044317715826722368780081)
                ·
                  refine ⟨783238286870041776585061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1044317715826722368780081 783238286870041776585061)
                  ·
                    refine ⟨146857178788132833109699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 783238286870041776585061 146857178788132833109699)
                    ·
                      rfl

theorem cell22_429005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_429005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_429005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_429005 prefixEnd_429005 := by exact prefixLift 429005
  have htrace : WordTrace (prefixWord ++ tailWord_429005) baseStart_429005 baseEnd_429005 := by
    simpa [prefixWord, tailWord_429005, baseEnd_429005] using wordTrace_append hprefix tailTrace_429005
  have hstable : (prefixWord ++ tailWord_429005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429005).length < 2 ^ (prefixWord ++ tailWord_429005).sum := by decide
  have hdescent : baseEnd_429005 < baseStart_429005 := by decide
  rcases family_descends (prefixWord ++ tailWord_429005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429087 : List Nat := [1, 1, 2, 4, 1, 4, 9]
def baseStart_429087 : Nat := 118140960795 + 429087 * 2 ^ 59
def prefixEnd_429087 : Nat := 4983230072969 + 3 ^ 40 * 429087 * 2
def baseEnd_429087 : Nat := 5440194409774516761461

theorem tailTrace_429087 : CollatzResearch.WordTrace tailWord_429087 prefixEnd_429087 5440194409774516761461 := by
  unfold tailWord_429087
  simp only [CollatzResearch.WordTrace]
  refine ⟨15650088596498556070413515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10433392397665704046942343 15650088596498556070413515)
  ·
    refine ⟨23475132894747834105620273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15650088596498556070413515 23475132894747834105620273)
    ·
      refine ⟨17606349671060875579215205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23475132894747834105620273 17606349671060875579215205)
      ·
        refine ⟨3301190563323914171102851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17606349671060875579215205 3301190563323914171102851)
        ·
          refine ⟨4951785844985871256654277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3301190563323914171102851 4951785844985871256654277)
          ·
            refine ⟨928459845934850860622677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4951785844985871256654277 928459845934850860622677)
            ·
              refine ⟨5440194409774516761461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 928459845934850860622677 5440194409774516761461)
              ·
                rfl

theorem cell22_429087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 9].length) (baseStart_429087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_429087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_429087 prefixEnd_429087 := by exact prefixLift 429087
  have htrace : WordTrace (prefixWord ++ tailWord_429087) baseStart_429087 baseEnd_429087 := by
    simpa [prefixWord, tailWord_429087, baseEnd_429087] using wordTrace_append hprefix tailTrace_429087
  have hstable : (prefixWord ++ tailWord_429087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429087).length < 2 ^ (prefixWord ++ tailWord_429087).sum := by decide
  have hdescent : baseEnd_429087 < baseStart_429087 := by decide
  rcases family_descends (prefixWord ++ tailWord_429087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429091 : List Nat := [1, 1, 1, 4, 3, 2, 3, 2, 2, 3]
def baseStart_429091 : Nat := 118140960795 + 429091 * 2 ^ 59
def prefixEnd_429091 : Nat := 4983230072969 + 3 ^ 40 * 429091 * 2
def baseEnd_429091 : Nat := 146886618345657275459435

theorem tailTrace_429091 : CollatzResearch.WordTrace tailWord_429091 prefixEnd_429091 146886618345657275459435 := by
  unfold tailWord_429091
  simp only [CollatzResearch.WordTrace]
  refine ⟨15650234488484064753559127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10433489658989376502372751 15650234488484064753559127)
  ·
    refine ⟨23475351732726097130338691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15650234488484064753559127 23475351732726097130338691)
    ·
      refine ⟨35213027599089145695508037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23475351732726097130338691 35213027599089145695508037)
      ·
        refine ⟨6602442674829214817907757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35213027599089145695508037 6602442674829214817907757)
        ·
          refine ⟨2475916003060955556715409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6602442674829214817907757 2475916003060955556715409)
          ·
            refine ⟨1856937002295716667536557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2475916003060955556715409 1856937002295716667536557)
            ·
              refine ⟨696351375860893750326209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1856937002295716667536557 696351375860893750326209)
              ·
                refine ⟨522263531895670312744657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 696351375860893750326209 522263531895670312744657)
                ·
                  refine ⟨391697648921752734558493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 522263531895670312744657 391697648921752734558493)
                  ·
                    refine ⟨146886618345657275459435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 391697648921752734558493 146886618345657275459435)
                    ·
                      rfl

theorem cell22_429091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 2, 3].length) (baseStart_429091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_429091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_429091 prefixEnd_429091 := by exact prefixLift 429091
  have htrace : WordTrace (prefixWord ++ tailWord_429091) baseStart_429091 baseEnd_429091 := by
    simpa [prefixWord, tailWord_429091, baseEnd_429091] using wordTrace_append hprefix tailTrace_429091
  have hstable : (prefixWord ++ tailWord_429091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429091).length < 2 ^ (prefixWord ++ tailWord_429091).sum := by decide
  have hdescent : baseEnd_429091 < baseStart_429091 := by decide
  rcases family_descends (prefixWord ++ tailWord_429091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429108 : List Nat := [2, 5, 1, 2, 1, 3, 1, 1, 1, 5]
def baseStart_429108 : Nat := 118140960795 + 429108 * 2 ^ 59
def prefixEnd_429108 : Nat := 4983230072969 + 3 ^ 40 * 429108 * 2
def baseEnd_429108 : Nat := 146892437793074897784383

theorem tailTrace_429108 : CollatzResearch.WordTrace tailWord_429108 prefixEnd_429108 146892437793074897784383 := by
  unfold tailWord_429108
  simp only [CollatzResearch.WordTrace]
  refine ⟨7825427264711238328463989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10433903019614984437951985 7825427264711238328463989)
  ·
    refine ⟨733633806066678593293499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7825427264711238328463989 733633806066678593293499)
    ·
      refine ⟨1100450709100017889940249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 733633806066678593293499 1100450709100017889940249)
      ·
        refine ⟨825338031825013417455187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1100450709100017889940249 825338031825013417455187)
        ·
          refine ⟨1238007047737520126182781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 825338031825013417455187 1238007047737520126182781)
          ·
            refine ⟨464252642901570047318543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1238007047737520126182781 464252642901570047318543)
            ·
              refine ⟨696378964352355070977815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 464252642901570047318543 696378964352355070977815)
              ·
                refine ⟨1044568446528532606466723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 696378964352355070977815 1044568446528532606466723)
                ·
                  refine ⟨1566852669792798909700085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1044568446528532606466723 1566852669792798909700085)
                  ·
                    refine ⟨146892437793074897784383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1566852669792798909700085 146892437793074897784383)
                    ·
                      rfl

theorem cell22_429108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_429108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_429108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_429108 prefixEnd_429108 := by exact prefixLift 429108
  have htrace : WordTrace (prefixWord ++ tailWord_429108) baseStart_429108 baseEnd_429108 := by
    simpa [prefixWord, tailWord_429108, baseEnd_429108] using wordTrace_append hprefix tailTrace_429108
  have hstable : (prefixWord ++ tailWord_429108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429108).length < 2 ^ (prefixWord ++ tailWord_429108).sum := by decide
  have hdescent : baseEnd_429108 < baseStart_429108 := by decide
  rcases family_descends (prefixWord ++ tailWord_429108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429166 : List Nat := [4, 1, 2, 2, 1, 3, 1, 3, 5]
def baseStart_429166 : Nat := 118140960795 + 429166 * 2 ^ 59
def prefixEnd_429166 : Nat := 4983230072969 + 3 ^ 40 * 429166 * 2
def baseEnd_429166 : Nat := 48970764126127359944735

theorem tailTrace_429166 : CollatzResearch.WordTrace tailWord_429166 prefixEnd_429166 48970764126127359944735 := by
  unfold tailWord_429166
  simp only [CollatzResearch.WordTrace]
  refine ⟨1956621245401544070317419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10435313308808235041692901 1956621245401544070317419)
  ·
    refine ⟨2934931868102316105476129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1956621245401544070317419 2934931868102316105476129)
    ·
      refine ⟨2201198901076737079107097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2934931868102316105476129 2201198901076737079107097)
      ·
        refine ⟨1650899175807552809330323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2201198901076737079107097 1650899175807552809330323)
        ·
          refine ⟨2476348763711329213995485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1650899175807552809330323 2476348763711329213995485)
          ·
            refine ⟨928630786391748455248307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2476348763711329213995485 928630786391748455248307)
            ·
              refine ⟨1392946179587622682872461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 928630786391748455248307 1392946179587622682872461)
              ·
                refine ⟨522354817345358506077173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1392946179587622682872461 522354817345358506077173)
                ·
                  refine ⟨48970764126127359944735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 522354817345358506077173 48970764126127359944735)
                  ·
                    rfl

theorem cell22_429166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_429166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_429166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_429166 prefixEnd_429166 := by exact prefixLift 429166
  have htrace : WordTrace (prefixWord ++ tailWord_429166) baseStart_429166 baseEnd_429166 := by
    simpa [prefixWord, tailWord_429166, baseEnd_429166] using wordTrace_append hprefix tailTrace_429166
  have hstable : (prefixWord ++ tailWord_429166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429166).length < 2 ^ (prefixWord ++ tailWord_429166).sum := by decide
  have hdescent : baseEnd_429166 < baseStart_429166 := by decide
  rcases family_descends (prefixWord ++ tailWord_429166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429241 : List Nat := [1, 2, 1, 4, 1, 3, 3, 1, 2, 4]
def baseStart_429241 : Nat := 118140960795 + 429241 * 2 ^ 59
def prefixEnd_429241 : Nat := 4983230072969 + 3 ^ 40 * 429241 * 2
def baseEnd_429241 : Nat := 146937966411106884208975

theorem tailTrace_429241 : CollatzResearch.WordTrace tailWord_429241 prefixEnd_429241 146937966411106884208975 := by
  unfold tailWord_429241
  simp only [CollatzResearch.WordTrace]
  refine ⟨15655705437940640371519577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10437136958627093581013051 15655705437940640371519577)
  ·
    refine ⟨11741779078455480278639683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15655705437940640371519577 11741779078455480278639683)
    ·
      refine ⟨17612668617683220417959525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11741779078455480278639683 17612668617683220417959525)
      ·
        refine ⟨3302375365815603828367411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17612668617683220417959525 3302375365815603828367411)
        ·
          refine ⟨4953563048723405742551117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3302375365815603828367411 4953563048723405742551117)
          ·
            refine ⟨1857586143271277153456669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4953563048723405742551117 1857586143271277153456669)
            ·
              refine ⟨696594803726728932546251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1857586143271277153456669 696594803726728932546251)
              ·
                refine ⟨1044892205590093398819377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 696594803726728932546251 1044892205590093398819377)
                ·
                  refine ⟨783669154192570049114533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1044892205590093398819377 783669154192570049114533)
                  ·
                    refine ⟨146937966411106884208975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 783669154192570049114533 146937966411106884208975)
                    ·
                      rfl

theorem cell22_429241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 4].length) (baseStart_429241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_429241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_429241 prefixEnd_429241 := by exact prefixLift 429241
  have htrace : WordTrace (prefixWord ++ tailWord_429241) baseStart_429241 baseEnd_429241 := by
    simpa [prefixWord, tailWord_429241, baseEnd_429241] using wordTrace_append hprefix tailTrace_429241
  have hstable : (prefixWord ++ tailWord_429241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429241).length < 2 ^ (prefixWord ++ tailWord_429241).sum := by decide
  have hdescent : baseEnd_429241 < baseStart_429241 := by decide
  rcases family_descends (prefixWord ++ tailWord_429241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429271 : List Nat := [1, 1, 3, 2, 1, 2, 3, 3, 3, 3]
def baseStart_429271 : Nat := 118140960795 + 429271 * 2 ^ 59
def prefixEnd_429271 : Nat := 4983230072969 + 3 ^ 40 * 429271 * 2
def baseEnd_429271 : Nat := 146948236024196805958883

theorem tailTrace_429271 : CollatzResearch.WordTrace tailWord_429271 prefixEnd_429271 146948236024196805958883 := by
  unfold tailWord_429271
  simp only [CollatzResearch.WordTrace]
  refine ⟨15656799627831955495111667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10437866418554636996741111 15656799627831955495111667)
  ·
    refine ⟨23485199441747933242667501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15656799627831955495111667 23485199441747933242667501)
    ·
      refine ⟨8806949790655474966000313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23485199441747933242667501 8806949790655474966000313)
      ·
        refine ⟨6605212342991606224500235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8806949790655474966000313 6605212342991606224500235)
        ·
          refine ⟨9907818514487409336750353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6605212342991606224500235 9907818514487409336750353)
          ·
            refine ⟨7430863885865557002562765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9907818514487409336750353 7430863885865557002562765)
            ·
              refine ⟨2786573957199583875961037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7430863885865557002562765 2786573957199583875961037)
              ·
                refine ⟨1044965233949843953485389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2786573957199583875961037 1044965233949843953485389)
                ·
                  refine ⟨391861962731191482557021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1044965233949843953485389 391861962731191482557021)
                  ·
                    refine ⟨146948236024196805958883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 391861962731191482557021 146948236024196805958883)
                    ·
                      rfl

theorem cell22_429271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 3, 3].length) (baseStart_429271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_429271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_429271 prefixEnd_429271 := by exact prefixLift 429271
  have htrace : WordTrace (prefixWord ++ tailWord_429271) baseStart_429271 baseEnd_429271 := by
    simpa [prefixWord, tailWord_429271, baseEnd_429271] using wordTrace_append hprefix tailTrace_429271
  have hstable : (prefixWord ++ tailWord_429271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429271).length < 2 ^ (prefixWord ++ tailWord_429271).sum := by decide
  have hdescent : baseEnd_429271 < baseStart_429271 := by decide
  rcases family_descends (prefixWord ++ tailWord_429271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429277 : List Nat := [1, 4, 3, 2, 2, 1, 3, 1, 2, 3]
def baseStart_429277 : Nat := 118140960795 + 429277 * 2 ^ 59
def prefixEnd_429277 : Nat := 4983230072969 + 3 ^ 40 * 429277 * 2
def baseEnd_429277 : Nat := 146950289946814790308865

theorem tailTrace_429277 : CollatzResearch.WordTrace tailWord_429277 prefixEnd_429277 146950289946814790308865 := by
  unfold tailWord_429277
  simp only [CollatzResearch.WordTrace]
  refine ⟨15657018465810218519830085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10438012310540145679886723 15657018465810218519830085)
  ·
    refine ⟨2935690962339415972468141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15657018465810218519830085 2935690962339415972468141)
    ·
      refine ⟨1100884110877280989675553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2935690962339415972468141 1100884110877280989675553)
      ·
        refine ⟨825663083157960742256665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1100884110877280989675553 825663083157960742256665)
        ·
          refine ⟨619247312368470556692499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 825663083157960742256665 619247312368470556692499)
          ·
            refine ⟨928870968552705835038749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619247312368470556692499 928870968552705835038749)
            ·
              refine ⟨348326613207264688139531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 928870968552705835038749 348326613207264688139531)
              ·
                refine ⟨522489919810897032209297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 348326613207264688139531 522489919810897032209297)
                ·
                  refine ⟨391867439858172774156973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 522489919810897032209297 391867439858172774156973)
                  ·
                    refine ⟨146950289946814790308865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 391867439858172774156973 146950289946814790308865)
                    ·
                      rfl

theorem cell22_429277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_429277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_429277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_429277 prefixEnd_429277 := by exact prefixLift 429277
  have htrace : WordTrace (prefixWord ++ tailWord_429277) baseStart_429277 baseEnd_429277 := by
    simpa [prefixWord, tailWord_429277, baseEnd_429277] using wordTrace_append hprefix tailTrace_429277
  have hstable : (prefixWord ++ tailWord_429277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429277).length < 2 ^ (prefixWord ++ tailWord_429277).sum := by decide
  have hdescent : baseEnd_429277 < baseStart_429277 := by decide
  rcases family_descends (prefixWord ++ tailWord_429277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429361 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 3, 5]
def baseStart_429361 : Nat := 118140960795 + 429361 * 2 ^ 59
def prefixEnd_429361 : Nat := 4983230072969 + 3 ^ 40 * 429361 * 2
def baseEnd_429361 : Nat := 146979044863466571208607

theorem tailTrace_429361 : CollatzResearch.WordTrace tailWord_429361 prefixEnd_429361 146979044863466571208607 := by
  unfold tailWord_429361
  simp only [CollatzResearch.WordTrace]
  refine ⟨15660082197505900865887937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10440054798337267243925291 15660082197505900865887937)
  ·
    refine ⟨11745061648129425649415953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15660082197505900865887937 11745061648129425649415953)
    ·
      refine ⟨8808796236097069237061965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11745061648129425649415953 8808796236097069237061965)
      ·
        refine ⟨3303298588536400963898237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8808796236097069237061965 3303298588536400963898237)
        ·
          refine ⟨1238736970701150361461839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3303298588536400963898237 1238736970701150361461839)
          ·
            refine ⟨1858105456051725542192759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1238736970701150361461839 1858105456051725542192759)
            ·
              refine ⟨2787158184077588313289139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1858105456051725542192759 2787158184077588313289139)
              ·
                refine ⟨4180737276116382469933709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2787158184077588313289139 4180737276116382469933709)
                ·
                  refine ⟨1567776478543643426225141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4180737276116382469933709 1567776478543643426225141)
                  ·
                    refine ⟨146979044863466571208607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1567776478543643426225141 146979044863466571208607)
                    ·
                      rfl

theorem cell22_429361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_429361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_429361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_429361 prefixEnd_429361 := by exact prefixLift 429361
  have htrace : WordTrace (prefixWord ++ tailWord_429361) baseStart_429361 baseEnd_429361 := by
    simpa [prefixWord, tailWord_429361, baseEnd_429361] using wordTrace_append hprefix tailTrace_429361
  have hstable : (prefixWord ++ tailWord_429361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429361).length < 2 ^ (prefixWord ++ tailWord_429361).sum := by decide
  have hdescent : baseEnd_429361 < baseStart_429361 := by decide
  rcases family_descends (prefixWord ++ tailWord_429361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429365 : List Nat := [1, 3, 3, 1, 2, 3, 3, 1, 1, 4]
def baseStart_429365 : Nat := 118140960795 + 429365 * 2 ^ 59
def prefixEnd_429365 : Nat := 4983230072969 + 3 ^ 40 * 429365 * 2
def baseEnd_429365 : Nat := 146980414145211894108595

theorem tailTrace_429365 : CollatzResearch.WordTrace tailWord_429365 prefixEnd_429365 146980414145211894108595 := by
  unfold tailWord_429365
  simp only [CollatzResearch.WordTrace]
  refine ⟨15660228089491409549033549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10440152059660939699355699 15660228089491409549033549)
  ·
    refine ⟨5872585533559278580887581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15660228089491409549033549 5872585533559278580887581)
    ·
      refine ⟨2202219575084729467832843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5872585533559278580887581 2202219575084729467832843)
      ·
        refine ⟨3303329362627094201749265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2202219575084729467832843 3303329362627094201749265)
        ·
          refine ⟨2477497021970320651311949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3303329362627094201749265 2477497021970320651311949)
          ·
            refine ⟨929061383238870244241981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2477497021970320651311949 929061383238870244241981)
            ·
              refine ⟨348398018714576341590743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 929061383238870244241981 348398018714576341590743)
              ·
                refine ⟨522597028071864512386115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 348398018714576341590743 522597028071864512386115)
                ·
                  refine ⟨783895542107796768579173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 522597028071864512386115 783895542107796768579173)
                  ·
                    refine ⟨146980414145211894108595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 783895542107796768579173 146980414145211894108595)
                    ·
                      rfl

theorem cell22_429365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_429365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_429365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_429365 prefixEnd_429365 := by exact prefixLift 429365
  have htrace : WordTrace (prefixWord ++ tailWord_429365) baseStart_429365 baseEnd_429365 := by
    simpa [prefixWord, tailWord_429365, baseEnd_429365] using wordTrace_append hprefix tailTrace_429365
  have hstable : (prefixWord ++ tailWord_429365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429365).length < 2 ^ (prefixWord ++ tailWord_429365).sum := by decide
  have hdescent : baseEnd_429365 < baseStart_429365 := by decide
  rcases family_descends (prefixWord ++ tailWord_429365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429376 : List Nat := [2, 1, 1, 2, 2, 1, 3, 4, 2, 4]
def baseStart_429376 : Nat := 118140960795 + 429376 * 2 ^ 59
def prefixEnd_429376 : Nat := 4983230072969 + 3 ^ 40 * 429376 * 2
def baseEnd_429376 : Nat := 146984179670011532083561

theorem tailTrace_429376 : CollatzResearch.WordTrace tailWord_429376 prefixEnd_429376 146984179670011532083561 := by
  unfold tailWord_429376
  simp only [CollatzResearch.WordTrace]
  refine ⟨7830314646225779213841991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10440419528301038951789321 7830314646225779213841991)
  ·
    refine ⟨11745471969338668820762987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7830314646225779213841991 11745471969338668820762987)
    ·
      refine ⟨17618207954008003231144481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11745471969338668820762987 17618207954008003231144481)
      ·
        refine ⟨13213655965506002423358361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17618207954008003231144481 13213655965506002423358361)
        ·
          refine ⟨9910241974129501817518771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13213655965506002423358361 9910241974129501817518771)
          ·
            refine ⟨14865362961194252726278157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9910241974129501817518771 14865362961194252726278157)
            ·
              refine ⟨5574511110447844772354309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14865362961194252726278157 5574511110447844772354309)
              ·
                refine ⟨1045220833208970894816433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5574511110447844772354309 1045220833208970894816433)
                ·
                  refine ⟨783915624906728171112325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1045220833208970894816433 783915624906728171112325)
                  ·
                    refine ⟨146984179670011532083561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 783915624906728171112325 146984179670011532083561)
                    ·
                      rfl

theorem cell22_429376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 2, 4].length) (baseStart_429376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_429376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_429376 prefixEnd_429376 := by exact prefixLift 429376
  have htrace : WordTrace (prefixWord ++ tailWord_429376) baseStart_429376 baseEnd_429376 := by
    simpa [prefixWord, tailWord_429376, baseEnd_429376] using wordTrace_append hprefix tailTrace_429376
  have hstable : (prefixWord ++ tailWord_429376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429376).length < 2 ^ (prefixWord ++ tailWord_429376).sum := by decide
  have hdescent : baseEnd_429376 < baseStart_429376 := by decide
  rcases family_descends (prefixWord ++ tailWord_429376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429408 : List Nat := [2, 1, 1, 3, 4, 2, 3, 6]
def baseStart_429408 : Nat := 118140960795 + 429408 * 2 ^ 59
def prefixEnd_429408 : Nat := 4983230072969 + 3 ^ 40 * 429408 * 2
def baseEnd_429408 : Nat := 16332792658219346142607

theorem tailTrace_429408 : CollatzResearch.WordTrace tailWord_429408 prefixEnd_429408 16332792658219346142607 := by
  unfold tailWord_429408
  simp only [CollatzResearch.WordTrace]
  refine ⟨7830898214167813946424439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10441197618890418595232585 7830898214167813946424439)
  ·
    refine ⟨11746347321251720919636659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7830898214167813946424439 11746347321251720919636659)
    ·
      refine ⟨17619520981877581379454989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11746347321251720919636659 17619520981877581379454989)
      ·
        refine ⟨6607320368204093017295621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17619520981877581379454989 6607320368204093017295621)
        ·
          refine ⟨1238872569038267440742929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6607320368204093017295621 1238872569038267440742929)
          ·
            refine ⟨929154426778700580557197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1238872569038267440742929 929154426778700580557197)
            ·
              refine ⟨348432910042012717708949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 929154426778700580557197 348432910042012717708949)
              ·
                refine ⟨16332792658219346142607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 348432910042012717708949 16332792658219346142607)
                ·
                  rfl

theorem cell22_429408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 6].length) (baseStart_429408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_429408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_429408 prefixEnd_429408 := by exact prefixLift 429408
  have htrace : WordTrace (prefixWord ++ tailWord_429408) baseStart_429408 baseEnd_429408 := by
    simpa [prefixWord, tailWord_429408, baseEnd_429408] using wordTrace_append hprefix tailTrace_429408
  have hstable : (prefixWord ++ tailWord_429408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429408).length < 2 ^ (prefixWord ++ tailWord_429408).sum := by decide
  have hdescent : baseEnd_429408 < baseStart_429408 := by decide
  rcases family_descends (prefixWord ++ tailWord_429408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429429 : List Nat := [1, 3, 4, 1, 4, 1, 1, 2, 2, 3]
def baseStart_429429 : Nat := 118140960795 + 429429 * 2 ^ 59
def prefixEnd_429429 : Nat := 4983230072969 + 3 ^ 40 * 429429 * 2
def baseEnd_429429 : Nat := 147002322653137060508399

theorem tailTrace_429429 : CollatzResearch.WordTrace tailWord_429429 prefixEnd_429429 147002322653137060508399 := by
  unfold tailWord_429429
  simp only [CollatzResearch.WordTrace]
  refine ⟨15662562361259548479363341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10441708240839698986242227 15662562361259548479363341)
  ·
    refine ⟨5873460885472330679761253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15662562361259548479363341 5873460885472330679761253)
    ·
      refine ⟨1101273916026062002455235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5873460885472330679761253 1101273916026062002455235)
      ·
        refine ⟨1651910874039093003682853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1101273916026062002455235 1651910874039093003682853)
        ·
          refine ⟨309733288882329938190535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1651910874039093003682853 309733288882329938190535)
          ·
            refine ⟨464599933323494907285803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309733288882329938190535 464599933323494907285803)
            ·
              refine ⟨696899899985242360928705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 464599933323494907285803 696899899985242360928705)
              ·
                refine ⟨522674924988931770696529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 696899899985242360928705 522674924988931770696529)
                ·
                  refine ⟨392006193741698828022397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 522674924988931770696529 392006193741698828022397)
                  ·
                    refine ⟨147002322653137060508399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 392006193741698828022397 147002322653137060508399)
                    ·
                      rfl

theorem cell22_429429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_429429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_429429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_429429 prefixEnd_429429 := by exact prefixLift 429429
  have htrace : WordTrace (prefixWord ++ tailWord_429429) baseStart_429429 baseEnd_429429 := by
    simpa [prefixWord, tailWord_429429, baseEnd_429429] using wordTrace_append hprefix tailTrace_429429
  have hstable : (prefixWord ++ tailWord_429429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429429).length < 2 ^ (prefixWord ++ tailWord_429429).sum := by decide
  have hdescent : baseEnd_429429 < baseStart_429429 := by decide
  rcases family_descends (prefixWord ++ tailWord_429429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429436 : List Nat := [2, 2, 2, 1, 1, 1, 5, 1, 7]
def baseStart_429436 : Nat := 118140960795 + 429436 * 2 ^ 59
def prefixEnd_429436 : Nat := 4983230072969 + 3 ^ 40 * 429436 * 2
def baseEnd_429436 : Nat := 49001572965397125194459

theorem tailTrace_429436 : CollatzResearch.WordTrace tailWord_429436 prefixEnd_429436 49001572965397125194459 := by
  unfold tailWord_429436
  simp only [CollatzResearch.WordTrace]
  refine ⟨7831408836117094337434081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10441878448156125783245441 7831408836117094337434081)
  ·
    refine ⟨5873556627087820753075561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7831408836117094337434081 5873556627087820753075561)
    ·
      refine ⟨4405167470315865564806671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5873556627087820753075561 4405167470315865564806671)
      ·
        refine ⟨6607751205473798347210007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4405167470315865564806671 6607751205473798347210007)
        ·
          refine ⟨9911626808210697520815011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6607751205473798347210007 9911626808210697520815011)
          ·
            refine ⟨14867440212316046281222517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9911626808210697520815011 14867440212316046281222517)
            ·
              refine ⟨1393822519904629338864611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14867440212316046281222517 1393822519904629338864611)
              ·
                refine ⟨2090733779856944008296917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1393822519904629338864611 2090733779856944008296917)
                ·
                  refine ⟨49001572965397125194459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2090733779856944008296917 49001572965397125194459)
                  ·
                    rfl

theorem cell22_429436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 7].length) (baseStart_429436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_429436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_429436 prefixEnd_429436 := by exact prefixLift 429436
  have htrace : WordTrace (prefixWord ++ tailWord_429436) baseStart_429436 baseEnd_429436 := by
    simpa [prefixWord, tailWord_429436, baseEnd_429436] using wordTrace_append hprefix tailTrace_429436
  have hstable : (prefixWord ++ tailWord_429436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429436).length < 2 ^ (prefixWord ++ tailWord_429436).sum := by decide
  have hdescent : baseEnd_429436 < baseStart_429436 := by decide
  rcases family_descends (prefixWord ++ tailWord_429436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429451 : List Nat := [1, 1, 1, 1, 4, 3, 1, 3, 2, 5]
def baseStart_429451 : Nat := 118140960795 + 429451 * 2 ^ 59
def prefixEnd_429451 : Nat := 4983230072969 + 3 ^ 40 * 429451 * 2
def baseEnd_429451 : Nat := 147009853702736336458331

theorem tailTrace_429451 : CollatzResearch.WordTrace tailWord_429451 prefixEnd_429451 147009853702736336458331 := by
  unfold tailWord_429451
  simp only [CollatzResearch.WordTrace]
  refine ⟨15663364767179846236664207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10442243178119897491109471 15663364767179846236664207)
  ·
    refine ⟨23495047150769769354996311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15663364767179846236664207 23495047150769769354996311)
    ·
      refine ⟨35242570726154654032494467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23495047150769769354996311 35242570726154654032494467)
      ·
        refine ⟨52863856089231981048741701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35242570726154654032494467 52863856089231981048741701)
        ·
          refine ⟨9911973016730996446639069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52863856089231981048741701 9911973016730996446639069)
          ·
            refine ⟨3716989881274123667489651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9911973016730996446639069 3716989881274123667489651)
            ·
              refine ⟨5575484821911185501234477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3716989881274123667489651 5575484821911185501234477)
              ·
                refine ⟨2090806808216694562962929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5575484821911185501234477 2090806808216694562962929)
                ·
                  refine ⟨1568105106162520922222197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2090806808216694562962929 1568105106162520922222197)
                  ·
                    refine ⟨147009853702736336458331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1568105106162520922222197 147009853702736336458331)
                    ·
                      rfl

theorem cell22_429451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 5].length) (baseStart_429451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_429451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_429451 prefixEnd_429451 := by exact prefixLift 429451
  have htrace : WordTrace (prefixWord ++ tailWord_429451) baseStart_429451 baseEnd_429451 := by
    simpa [prefixWord, tailWord_429451, baseEnd_429451] using wordTrace_append hprefix tailTrace_429451
  have hstable : (prefixWord ++ tailWord_429451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429451).length < 2 ^ (prefixWord ++ tailWord_429451).sum := by decide
  have hdescent : baseEnd_429451 < baseStart_429451 := by decide
  rcases family_descends (prefixWord ++ tailWord_429451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429474 : List Nat := [3, 3, 1, 2, 1, 4, 1, 3, 1, 3]
def baseStart_429474 : Nat := 118140960795 + 429474 * 2 ^ 59
def prefixEnd_429474 : Nat := 4983230072969 + 3 ^ 40 * 429474 * 2
def baseEnd_429474 : Nat := 147017727072771943133261

theorem tailTrace_429474 : CollatzResearch.WordTrace tailWord_429474 prefixEnd_429474 147017727072771943133261 := by
  unfold tailWord_429474
  simp only [CollatzResearch.WordTrace]
  refine ⟨3916050911524130291187869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10442802430731014109834317 3916050911524130291187869)
  ·
    refine ⟨1468519091821548859195451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3916050911524130291187869 1468519091821548859195451)
    ·
      refine ⟨2202778637732323288793177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1468519091821548859195451 2202778637732323288793177)
      ·
        refine ⟨1652083978299242466594883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2202778637732323288793177 1652083978299242466594883)
        ·
          refine ⟨2478125967448863699892325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1652083978299242466594883 2478125967448863699892325)
          ·
            refine ⟨464648618896661943729811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2478125967448863699892325 464648618896661943729811)
            ·
              refine ⟨696972928344992915594717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 464648618896661943729811 696972928344992915594717)
              ·
                refine ⟨261364848129372343348019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 696972928344992915594717 261364848129372343348019)
                ·
                  refine ⟨392047272194058515022029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 261364848129372343348019 392047272194058515022029)
                  ·
                    refine ⟨147017727072771943133261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 392047272194058515022029 147017727072771943133261)
                    ·
                      rfl

theorem cell22_429474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_429474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_429474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_429474 prefixEnd_429474 := by exact prefixLift 429474
  have htrace : WordTrace (prefixWord ++ tailWord_429474) baseStart_429474 baseEnd_429474 := by
    simpa [prefixWord, tailWord_429474, baseEnd_429474] using wordTrace_append hprefix tailTrace_429474
  have hstable : (prefixWord ++ tailWord_429474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429474).length < 2 ^ (prefixWord ++ tailWord_429474).sum := by decide
  have hdescent : baseEnd_429474 < baseStart_429474 := by decide
  rcases family_descends (prefixWord ++ tailWord_429474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429528 : List Nat := [2, 1, 2, 2, 2, 1, 3, 3, 2, 4]
def baseStart_429528 : Nat := 118140960795 + 429528 * 2 ^ 59
def prefixEnd_429528 : Nat := 4983230072969 + 3 ^ 40 * 429528 * 2
def baseEnd_429528 : Nat := 147036212376333802283095

theorem tailTrace_429528 : CollatzResearch.WordTrace tailWord_429528 prefixEnd_429528 147036212376333802283095 := by
  unfold tailWord_429528
  simp only [CollatzResearch.WordTrace]
  refine ⟨7833086593950444193608619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10444115458600592258144825 7833086593950444193608619)
  ·
    refine ⟨11749629890925666290412929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7833086593950444193608619 11749629890925666290412929)
    ·
      refine ⟨8812222418194249717809697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11749629890925666290412929 8812222418194249717809697)
      ·
        refine ⟨6609166813645687288357273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8812222418194249717809697 6609166813645687288357273)
        ·
          refine ⟨4956875110234265466267955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6609166813645687288357273 4956875110234265466267955)
          ·
            refine ⟨7435312665351398199401933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4956875110234265466267955 7435312665351398199401933)
            ·
              refine ⟨2788242249506774324775725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7435312665351398199401933 2788242249506774324775725)
              ·
                refine ⟨1045590843565040371790897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2788242249506774324775725 1045590843565040371790897)
                ·
                  refine ⟨784193132673780278843173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1045590843565040371790897 784193132673780278843173)
                  ·
                    refine ⟨147036212376333802283095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 784193132673780278843173 147036212376333802283095)
                    ·
                      rfl

theorem cell22_429528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_429528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_429528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_429528 prefixEnd_429528 := by exact prefixLift 429528
  have htrace : WordTrace (prefixWord ++ tailWord_429528) baseStart_429528 baseEnd_429528 := by
    simpa [prefixWord, tailWord_429528, baseEnd_429528] using wordTrace_append hprefix tailTrace_429528
  have hstable : (prefixWord ++ tailWord_429528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429528).length < 2 ^ (prefixWord ++ tailWord_429528).sum := by decide
  have hdescent : baseEnd_429528 < baseStart_429528 := by decide
  rcases family_descends (prefixWord ++ tailWord_429528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429575 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 5, 3]
def baseStart_429575 : Nat := 118140960795 + 429575 * 2 ^ 59
def prefixEnd_429575 : Nat := 4983230072969 + 3 ^ 40 * 429575 * 2
def baseEnd_429575 : Nat := 147052301436841346357951

theorem tailTrace_429575 : CollatzResearch.WordTrace tailWord_429575 prefixEnd_429575 147052301436841346357951 := by
  unfold tailWord_429575
  simp only [CollatzResearch.WordTrace]
  refine ⟨15667887418730615414178179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10445258279153743609452119 15667887418730615414178179)
  ·
    refine ⟨23501831128095923121267269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15667887418730615414178179 23501831128095923121267269)
    ·
      refine ⟨4406593336517985585237613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23501831128095923121267269 4406593336517985585237613)
      ·
        refine ⟨1652472501194244594464105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4406593336517985585237613 1652472501194244594464105)
        ·
          refine ⟨1239354375895683445848079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1652472501194244594464105 1239354375895683445848079)
          ·
            refine ⟨1859031563843525168772119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1239354375895683445848079 1859031563843525168772119)
            ·
              refine ⟨2788547345765287753158179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1859031563843525168772119 2788547345765287753158179)
              ·
                refine ⟨4182821018647931629737269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2788547345765287753158179 4182821018647931629737269)
                ·
                  refine ⟨392139470498243590287869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4182821018647931629737269 392139470498243590287869)
                  ·
                    refine ⟨147052301436841346357951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 392139470498243590287869 147052301436841346357951)
                    ·
                      rfl

theorem cell22_429575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_429575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_429575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_429575 prefixEnd_429575 := by exact prefixLift 429575
  have htrace : WordTrace (prefixWord ++ tailWord_429575) baseStart_429575 baseEnd_429575 := by
    simpa [prefixWord, tailWord_429575, baseEnd_429575] using wordTrace_append hprefix tailTrace_429575
  have hstable : (prefixWord ++ tailWord_429575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429575).length < 2 ^ (prefixWord ++ tailWord_429575).sum := by decide
  have hdescent : baseEnd_429575 < baseStart_429575 := by decide
  rcases family_descends (prefixWord ++ tailWord_429575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429648 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 3, 5]
def baseStart_429648 : Nat := 118140960795 + 429648 * 2 ^ 59
def prefixEnd_429648 : Nat := 4983230072969 + 3 ^ 40 * 429648 * 2
def baseEnd_429648 : Nat := 147077290828693489282727

theorem tailTrace_429648 : CollatzResearch.WordTrace tailWord_429648 prefixEnd_429648 147077290828693489282727 := by
  unfold tailWord_429648
  simp only [CollatzResearch.WordTrace]
  refine ⟨7835274973733074440792799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10447033298310765921057065 7835274973733074440792799)
  ·
    refine ⟨11752912460599611661189199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7835274973733074440792799 11752912460599611661189199)
    ·
      refine ⟨17629368690899417491783799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11752912460599611661189199 17629368690899417491783799)
      ·
        refine ⟨26444053036349126237675699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17629368690899417491783799 26444053036349126237675699)
        ·
          refine ⟨39666079554523689356513549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26444053036349126237675699 39666079554523689356513549)
          ·
            refine ⟨14874779832946383508692581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39666079554523689356513549 14874779832946383508692581)
            ·
              refine ⟨2789021218677446907879859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14874779832946383508692581 2789021218677446907879859)
              ·
                refine ⟨4183531828016170361819789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2789021218677446907879859 4183531828016170361819789)
                ·
                  refine ⟨1568824435506063885682421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4183531828016170361819789 1568824435506063885682421)
                  ·
                    refine ⟨147077290828693489282727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1568824435506063885682421 147077290828693489282727)
                    ·
                      rfl

theorem cell22_429648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 3, 5].length) (baseStart_429648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_429648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_429648 prefixEnd_429648 := by exact prefixLift 429648
  have htrace : WordTrace (prefixWord ++ tailWord_429648) baseStart_429648 baseEnd_429648 := by
    simpa [prefixWord, tailWord_429648, baseEnd_429648] using wordTrace_append hprefix tailTrace_429648
  have hstable : (prefixWord ++ tailWord_429648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429648).length < 2 ^ (prefixWord ++ tailWord_429648).sum := by decide
  have hdescent : baseEnd_429648 < baseStart_429648 := by decide
  rcases family_descends (prefixWord ++ tailWord_429648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429665 : List Nat := [1, 2, 3, 1, 1, 3, 1, 3, 4, 3]
def baseStart_429665 : Nat := 118140960795 + 429665 * 2 ^ 59
def prefixEnd_429665 : Nat := 4983230072969 + 3 ^ 40 * 429665 * 2
def baseEnd_429665 : Nat := 147083110276111111607675

theorem tailTrace_429665 : CollatzResearch.WordTrace tailWord_429665 prefixEnd_429665 147083110276111111607675 := by
  unfold tailWord_429665
  simp only [CollatzResearch.WordTrace]
  refine ⟨15671169988404560784954449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10447446658936373856636299 15671169988404560784954449)
  ·
    refine ⟨11753377491303420588715837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15671169988404560784954449 11753377491303420588715837)
    ·
      refine ⟨4407516559238782720768439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11753377491303420588715837 4407516559238782720768439)
      ·
        refine ⟨6611274838858174081152659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4407516559238782720768439 6611274838858174081152659)
        ·
          refine ⟨9916912258287261121728989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6611274838858174081152659 9916912258287261121728989)
          ·
            refine ⟨3718842096857722920648371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9916912258287261121728989 3718842096857722920648371)
            ·
              refine ⟨5578263145286584380972557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3718842096857722920648371 5578263145286584380972557)
              ·
                refine ⟨2091848679482469142864709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5578263145286584380972557 2091848679482469142864709)
                ·
                  refine ⟨392221627402962964287133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2091848679482469142864709 392221627402962964287133)
                  ·
                    refine ⟨147083110276111111607675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 392221627402962964287133 147083110276111111607675)
                    ·
                      rfl

theorem cell22_429665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_429665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_429665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_429665 prefixEnd_429665 := by exact prefixLift 429665
  have htrace : WordTrace (prefixWord ++ tailWord_429665) baseStart_429665 baseEnd_429665 := by
    simpa [prefixWord, tailWord_429665, baseEnd_429665] using wordTrace_append hprefix tailTrace_429665
  have hstable : (prefixWord ++ tailWord_429665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429665).length < 2 ^ (prefixWord ++ tailWord_429665).sum := by decide
  have hdescent : baseEnd_429665 < baseStart_429665 := by decide
  rcases family_descends (prefixWord ++ tailWord_429665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429697 : List Nat := [1, 2, 4, 2, 1, 3, 2, 1, 2, 4]
def baseStart_429697 : Nat := 118140960795 + 429697 * 2 ^ 59
def prefixEnd_429697 : Nat := 4983230072969 + 3 ^ 40 * 429697 * 2
def baseEnd_429697 : Nat := 147094064530073694807577

theorem tailTrace_429697 : CollatzResearch.WordTrace tailWord_429697 prefixEnd_429697 147094064530073694807577 := by
  unfold tailWord_429697
  simp only [CollatzResearch.WordTrace]
  refine ⟨15672337124288630250119345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10448224749525753500079563 15672337124288630250119345)
  ·
    refine ⟨11754252843216472687589509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15672337124288630250119345 11754252843216472687589509)
    ·
      refine ⟨2203922408103088628923033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11754252843216472687589509 2203922408103088628923033)
      ·
        refine ⟨1652941806077316471692275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2203922408103088628923033 1652941806077316471692275)
        ·
          refine ⟨2479412709115974707538413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1652941806077316471692275 2479412709115974707538413)
          ·
            refine ⟨929779765918490515326905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2479412709115974707538413 929779765918490515326905)
            ·
              refine ⟨697334824438867886495179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 929779765918490515326905 697334824438867886495179)
              ·
                refine ⟨1046002236658301829742769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 697334824438867886495179 1046002236658301829742769)
                ·
                  refine ⟨784501677493726372307077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1046002236658301829742769 784501677493726372307077)
                  ·
                    refine ⟨147094064530073694807577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 784501677493726372307077 147094064530073694807577)
                    ·
                      rfl

theorem cell22_429697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_429697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_429697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_429697 prefixEnd_429697 := by exact prefixLift 429697
  have htrace : WordTrace (prefixWord ++ tailWord_429697) baseStart_429697 baseEnd_429697 := by
    simpa [prefixWord, tailWord_429697, baseEnd_429697] using wordTrace_append hprefix tailTrace_429697
  have hstable : (prefixWord ++ tailWord_429697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429697).length < 2 ^ (prefixWord ++ tailWord_429697).sum := by decide
  have hdescent : baseEnd_429697 < baseStart_429697 := by decide
  rcases family_descends (prefixWord ++ tailWord_429697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429716 : List Nat := [2, 4, 2, 2, 2, 1, 2, 2, 2, 3]
def baseStart_429716 : Nat := 118140960795 + 429716 * 2 ^ 59
def prefixEnd_429716 : Nat := 4983230072969 + 3 ^ 40 * 429716 * 2
def baseEnd_429716 : Nat := 147100568618363978582519

theorem tailTrace_429716 : CollatzResearch.WordTrace tailWord_429716 prefixEnd_429716 147100568618363978582519 := by
  unfold tailWord_429716
  simp only [CollatzResearch.WordTrace]
  refine ⟨7836515055609898247530501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10448686740813197663374001 7836515055609898247530501)
  ·
    refine ⟨1469346572926855921411969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7836515055609898247530501 1469346572926855921411969)
    ·
      refine ⟨1102009929695141941058977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1469346572926855921411969 1102009929695141941058977)
      ·
        refine ⟨826507447271356455794233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1102009929695141941058977 826507447271356455794233)
        ·
          refine ⟨619880585453517341845675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 826507447271356455794233 619880585453517341845675)
          ·
            refine ⟨929820878180276012768513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619880585453517341845675 929820878180276012768513)
            ·
              refine ⟨697365658635207009576385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 929820878180276012768513 697365658635207009576385)
              ·
                refine ⟨523024243976405257182289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 697365658635207009576385 523024243976405257182289)
                ·
                  refine ⟨392268182982303942886717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 523024243976405257182289 392268182982303942886717)
                  ·
                    refine ⟨147100568618363978582519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 392268182982303942886717 147100568618363978582519)
                    ·
                      rfl

theorem cell22_429716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_429716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_429716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_429716 prefixEnd_429716 := by exact prefixLift 429716
  have htrace : WordTrace (prefixWord ++ tailWord_429716) baseStart_429716 baseEnd_429716 := by
    simpa [prefixWord, tailWord_429716, baseEnd_429716] using wordTrace_append hprefix tailTrace_429716
  have hstable : (prefixWord ++ tailWord_429716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429716).length < 2 ^ (prefixWord ++ tailWord_429716).sum := by decide
  have hdescent : baseEnd_429716 < baseStart_429716 := by decide
  rcases family_descends (prefixWord ++ tailWord_429716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429785 : List Nat := [1, 2, 1, 2, 3, 3, 1, 3, 6]
def baseStart_429785 : Nat := 118140960795 + 429785 * 2 ^ 59
def prefixEnd_429785 : Nat := 4983230072969 + 3 ^ 40 * 429785 * 2
def baseEnd_429785 : Nat := 49041396242823599535769

theorem tailTrace_429785 : CollatzResearch.WordTrace tailWord_429785 prefixEnd_429785 49041396242823599535769 := by
  unfold tailWord_429785
  simp only [CollatzResearch.WordTrace]
  refine ⟨15675546747969821279322809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10450364498646547519548539 15675546747969821279322809)
  ·
    refine ⟨11756660060977365959492107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15675546747969821279322809 11756660060977365959492107)
    ·
      refine ⟨17634990091466048939238161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11756660060977365959492107 17634990091466048939238161)
      ·
        refine ⟨13226242568599536704428621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17634990091466048939238161 13226242568599536704428621)
        ·
          refine ⟨4959840963224826264160733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13226242568599536704428621 4959840963224826264160733)
          ·
            refine ⟨1859940361209309849060275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4959840963224826264160733 1859940361209309849060275)
            ·
              refine ⟨2789910541813964773590413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1859940361209309849060275 2789910541813964773590413)
              ·
                refine ⟨1046216453180236790096405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2789910541813964773590413 1046216453180236790096405)
                ·
                  refine ⟨49041396242823599535769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1046216453180236790096405 49041396242823599535769)
                  ·
                    rfl

theorem cell22_429785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 6].length) (baseStart_429785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_429785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_429785 prefixEnd_429785 := by exact prefixLift 429785
  have htrace : WordTrace (prefixWord ++ tailWord_429785) baseStart_429785 baseEnd_429785 := by
    simpa [prefixWord, tailWord_429785, baseEnd_429785] using wordTrace_append hprefix tailTrace_429785
  have hstable : (prefixWord ++ tailWord_429785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429785).length < 2 ^ (prefixWord ++ tailWord_429785).sum := by decide
  have hdescent : baseEnd_429785 < baseStart_429785 := by decide
  rcases family_descends (prefixWord ++ tailWord_429785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429815 : List Nat := [1, 1, 3, 1, 1, 1, 6, 1, 1, 6]
def baseStart_429815 : Nat := 118140960795 + 429815 * 2 ^ 59
def prefixEnd_429815 : Nat := 4983230072969 + 3 ^ 40 * 429815 * 2
def baseEnd_429815 : Nat := 147134458341560720357215

theorem tailTrace_429815 : CollatzResearch.WordTrace tailWord_429815 prefixEnd_429815 147134458341560720357215 := by
  unfold tailWord_429815
  simp only [CollatzResearch.WordTrace]
  refine ⟨15676640937861136402914899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10451093958574090935276599 15676640937861136402914899)
  ·
    refine ⟨23514961406791704604372349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15676640937861136402914899 23514961406791704604372349)
    ·
      refine ⟨8818110527546889226639631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23514961406791704604372349 8818110527546889226639631)
      ·
        refine ⟨13227165791320333839959447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8818110527546889226639631 13227165791320333839959447)
        ·
          refine ⟨19840748686980500759939171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13227165791320333839959447 19840748686980500759939171)
          ·
            refine ⟨29761123030470751139908757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19840748686980500759939171 29761123030470751139908757)
            ·
              refine ⟨1395052642053316459683223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29761123030470751139908757 1395052642053316459683223)
              ·
                refine ⟨2092578963079974689524835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1395052642053316459683223 2092578963079974689524835)
                ·
                  refine ⟨3138868444619962034287253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2092578963079974689524835 3138868444619962034287253)
                  ·
                    refine ⟨147134458341560720357215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3138868444619962034287253 147134458341560720357215)
                    ·
                      rfl

theorem cell22_429815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_429815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_429815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_429815 prefixEnd_429815 := by exact prefixLift 429815
  have htrace : WordTrace (prefixWord ++ tailWord_429815) baseStart_429815 baseEnd_429815 := by
    simpa [prefixWord, tailWord_429815, baseEnd_429815] using wordTrace_append hprefix tailTrace_429815
  have hstable : (prefixWord ++ tailWord_429815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429815).length < 2 ^ (prefixWord ++ tailWord_429815).sum := by decide
  have hdescent : baseEnd_429815 < baseStart_429815 := by decide
  rcases family_descends (prefixWord ++ tailWord_429815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429832 : List Nat := [2, 1, 3, 2, 2, 1, 3, 2, 2, 4]
def baseStart_429832 : Nat := 118140960795 + 429832 * 2 ^ 59
def prefixEnd_429832 : Nat := 4983230072969 + 3 ^ 40 * 429832 * 2
def baseEnd_429832 : Nat := 147140277788978342682163

theorem tailTrace_429832 : CollatzResearch.WordTrace tailWord_429832 prefixEnd_429832 147140277788978342682163 := by
  unfold tailWord_429832
  simp only [CollatzResearch.WordTrace]
  refine ⟨7838630489399774153141875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10451507319199698870855833 7838630489399774153141875)
  ·
    refine ⟨11757945734099661229712813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7838630489399774153141875 11757945734099661229712813)
    ·
      refine ⟨4409229650287372961142305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11757945734099661229712813 4409229650287372961142305)
      ·
        refine ⟨3306922237715529720856729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4409229650287372961142305 3306922237715529720856729)
        ·
          refine ⟨2480191678286647290642547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3306922237715529720856729 2480191678286647290642547)
          ·
            refine ⟨3720287517429970935963821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2480191678286647290642547 3720287517429970935963821)
            ·
              refine ⟨1395107819036239100986433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3720287517429970935963821 1395107819036239100986433)
              ·
                refine ⟨1046330864277179325739825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1395107819036239100986433 1046330864277179325739825)
                ·
                  refine ⟨784748148207884494304869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1046330864277179325739825 784748148207884494304869)
                  ·
                    refine ⟨147140277788978342682163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 784748148207884494304869 147140277788978342682163)
                    ·
                      rfl

theorem cell22_429832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_429832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_429832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_429832 prefixEnd_429832 := by exact prefixLift 429832
  have htrace : WordTrace (prefixWord ++ tailWord_429832) baseStart_429832 baseEnd_429832 := by
    simpa [prefixWord, tailWord_429832, baseEnd_429832] using wordTrace_append hprefix tailTrace_429832
  have hstable : (prefixWord ++ tailWord_429832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429832).length < 2 ^ (prefixWord ++ tailWord_429832).sum := by decide
  have hdescent : baseEnd_429832 < baseStart_429832 := by decide
  rcases family_descends (prefixWord ++ tailWord_429832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429847 : List Nat := [1, 1, 3, 4, 2, 2, 2, 7]
def baseStart_429847 : Nat := 118140960795 + 429847 * 2 ^ 59
def prefixEnd_429847 : Nat := 4983230072969 + 3 ^ 40 * 429847 * 2
def baseEnd_429847 : Nat := 16349490288391478173013

theorem tailTrace_429847 : CollatzResearch.WordTrace tailWord_429847 prefixEnd_429847 16349490288391478173013 := by
  unfold tailWord_429847
  simp only [CollatzResearch.WordTrace]
  refine ⟨15677808073745205868079795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10451872049163470578719863 15677808073745205868079795)
  ·
    refine ⟨23516712110617808802119693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15677808073745205868079795 23516712110617808802119693)
    ·
      refine ⟨8818767041481678300794885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23516712110617808802119693 8818767041481678300794885)
      ·
        refine ⟨1653518820277814681399041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8818767041481678300794885 1653518820277814681399041)
        ·
          refine ⟨1240139115208361011049281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1653518820277814681399041 1240139115208361011049281)
          ·
            refine ⟨930104336406270758286961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1240139115208361011049281 930104336406270758286961)
            ·
              refine ⟨697578252304703068715221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 930104336406270758286961 697578252304703068715221)
              ·
                refine ⟨16349490288391478173013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 697578252304703068715221 16349490288391478173013)
                ·
                  rfl

theorem cell22_429847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 7].length) (baseStart_429847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_429847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_429847 prefixEnd_429847 := by exact prefixLift 429847
  have htrace : WordTrace (prefixWord ++ tailWord_429847) baseStart_429847 baseEnd_429847 := by
    simpa [prefixWord, tailWord_429847, baseEnd_429847] using wordTrace_append hprefix tailTrace_429847
  have hstable : (prefixWord ++ tailWord_429847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429847).length < 2 ^ (prefixWord ++ tailWord_429847).sum := by decide
  have hdescent : baseEnd_429847 < baseStart_429847 := by decide
  rcases family_descends (prefixWord ++ tailWord_429847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429896 : List Nat := [2, 1, 3, 1, 1, 5, 1, 4, 1, 3]
def baseStart_429896 : Nat := 118140960795 + 429896 * 2 ^ 59
def prefixEnd_429896 : Nat := 4983230072969 + 3 ^ 40 * 429896 * 2
def baseEnd_429896 : Nat := 147162186296903509081967

theorem tailTrace_429896 : CollatzResearch.WordTrace tailWord_429896 prefixEnd_429896 147162186296903509081967 := by
  unfold tailWord_429896
  simp only [CollatzResearch.WordTrace]
  refine ⟨7839797625283843618306771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10453063500378458157742361 7839797625283843618306771)
  ·
    refine ⟨11759696437925765427460157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7839797625283843618306771 11759696437925765427460157)
    ·
      refine ⟨4409886164222162035297559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11759696437925765427460157 4409886164222162035297559)
      ·
        refine ⟨6614829246333243052946339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4409886164222162035297559 6614829246333243052946339)
        ·
          refine ⟨9922243869499864579419509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6614829246333243052946339 9922243869499864579419509)
          ·
            refine ⟨930210362765612304320579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9922243869499864579419509 930210362765612304320579)
            ·
              refine ⟨1395315544148418456480869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 930210362765612304320579 1395315544148418456480869)
              ·
                refine ⟨261621664527828460590163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1395315544148418456480869 261621664527828460590163)
                ·
                  refine ⟨392432496791742690885245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 261621664527828460590163 392432496791742690885245)
                  ·
                    refine ⟨147162186296903509081967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 392432496791742690885245 147162186296903509081967)
                    ·
                      rfl

theorem cell22_429896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 4, 1, 3].length) (baseStart_429896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_429896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_429896 prefixEnd_429896 := by exact prefixLift 429896
  have htrace : WordTrace (prefixWord ++ tailWord_429896) baseStart_429896 baseEnd_429896 := by
    simpa [prefixWord, tailWord_429896, baseEnd_429896] using wordTrace_append hprefix tailTrace_429896
  have hstable : (prefixWord ++ tailWord_429896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429896).length < 2 ^ (prefixWord ++ tailWord_429896).sum := by decide
  have hdescent : baseEnd_429896 < baseStart_429896 := by decide
  rcases family_descends (prefixWord ++ tailWord_429896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429930 : List Nat := [3, 1, 3, 4, 1, 1, 2, 3, 1, 3]
def baseStart_429930 : Nat := 118140960795 + 429930 * 2 ^ 59
def prefixEnd_429930 : Nat := 4983230072969 + 3 ^ 40 * 429930 * 2
def baseEnd_429930 : Nat := 147173825191738753731863

theorem tailTrace_429930 : CollatzResearch.WordTrace tailWord_429930 prefixEnd_429930 147173825191738753731863 := by
  unfold tailWord_429930
  simp only [CollatzResearch.WordTrace]
  refine ⟨3920208833111127760837811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10453890221629674028900829 3920208833111127760837811)
  ·
    refine ⟨5880313249666691641256717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3920208833111127760837811 5880313249666691641256717)
    ·
      refine ⟨2205117468625009365471269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5880313249666691641256717 2205117468625009365471269)
      ·
        refine ⟨413459525367189256025863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2205117468625009365471269 413459525367189256025863)
        ·
          refine ⟨620189288050783884038795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413459525367189256025863 620189288050783884038795)
          ·
            refine ⟨930283932076175826058193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620189288050783884038795 930283932076175826058193)
            ·
              refine ⟨697712949057131869543645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 930283932076175826058193 697712949057131869543645)
              ·
                refine ⟨261642355896424451078867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 697712949057131869543645 261642355896424451078867)
                ·
                  refine ⟨392463533844636676618301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 261642355896424451078867 392463533844636676618301)
                  ·
                    refine ⟨147173825191738753731863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 392463533844636676618301 147173825191738753731863)
                    ·
                      rfl

theorem cell22_429930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_429930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_429930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_429930 prefixEnd_429930 := by exact prefixLift 429930
  have htrace : WordTrace (prefixWord ++ tailWord_429930) baseStart_429930 baseEnd_429930 := by
    simpa [prefixWord, tailWord_429930, baseEnd_429930] using wordTrace_append hprefix tailTrace_429930
  have hstable : (prefixWord ++ tailWord_429930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429930).length < 2 ^ (prefixWord ++ tailWord_429930).sum := by decide
  have hdescent : baseEnd_429930 < baseStart_429930 := by decide
  rcases family_descends (prefixWord ++ tailWord_429930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_429969 : List Nat := [1, 2, 2, 1, 1, 1, 4, 5, 2, 3]
def baseStart_429969 : Nat := 118140960795 + 429969 * 2 ^ 59
def prefixEnd_429969 : Nat := 4983230072969 + 3 ^ 40 * 429969 * 2
def baseEnd_429969 : Nat := 147187175688755652006743

theorem tailTrace_429969 : CollatzResearch.WordTrace tailWord_429969 prefixEnd_429969 147187175688755652006743 := by
  unfold tailWord_429969
  simp only [CollatzResearch.WordTrace]
  refine ⟨15682257779303220704020961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10454838519535480469347307 15682257779303220704020961)
  ·
    refine ⟨11761693334477415528015721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15682257779303220704020961 11761693334477415528015721)
    ·
      refine ⟨8821270000858061646011791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11761693334477415528015721 8821270000858061646011791)
      ·
        refine ⟨13231905001287092469017687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8821270000858061646011791 13231905001287092469017687)
        ·
          refine ⟨19847857501930638703526531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13231905001287092469017687 19847857501930638703526531)
          ·
            refine ⟨29771786252895958055289797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19847857501930638703526531 29771786252895958055289797)
            ·
              refine ⟨5582209922417992135366837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29771786252895958055289797 5582209922417992135366837)
              ·
                refine ⟨523332180226686762690641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5582209922417992135366837 523332180226686762690641)
                ·
                  refine ⟨392499135170015072017981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 523332180226686762690641 392499135170015072017981)
                  ·
                    refine ⟨147187175688755652006743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 392499135170015072017981 147187175688755652006743)
                    ·
                      rfl

theorem cell22_429969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 2, 3].length) (baseStart_429969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_429969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_429969 prefixEnd_429969 := by exact prefixLift 429969
  have htrace : WordTrace (prefixWord ++ tailWord_429969) baseStart_429969 baseEnd_429969 := by
    simpa [prefixWord, tailWord_429969, baseEnd_429969] using wordTrace_append hprefix tailTrace_429969
  have hstable : (prefixWord ++ tailWord_429969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_429969).length < 2 ^ (prefixWord ++ tailWord_429969).sum := by decide
  have hdescent : baseEnd_429969 < baseStart_429969 := by decide
  rcases family_descends (prefixWord ++ tailWord_429969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430104 : List Nat := [2, 1, 2, 3, 2, 1, 1, 4, 1, 5]
def baseStart_430104 : Nat := 118140960795 + 430104 * 2 ^ 59
def prefixEnd_430104 : Nat := 4983230072969 + 3 ^ 40 * 430104 * 2
def baseEnd_430104 : Nat := 147233388947660299881329

theorem tailTrace_430104 : CollatzResearch.WordTrace tailWord_430104 prefixEnd_430104 147233388947660299881329 := by
  unfold tailWord_430104
  simp only [CollatzResearch.WordTrace]
  refine ⟨7843590816907069380092683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10458121089209425840123577 7843590816907069380092683)
  ·
    refine ⟨11765386225360604070139025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7843590816907069380092683 11765386225360604070139025)
    ·
      refine ⟨8824039669020453052604269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11765386225360604070139025 8824039669020453052604269)
      ·
        refine ⟨3309014875882669894726601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8824039669020453052604269 3309014875882669894726601)
        ·
          refine ⟨2481761156912002421044951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3309014875882669894726601 2481761156912002421044951)
          ·
            refine ⟨3722641735368003631567427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2481761156912002421044951 3722641735368003631567427)
            ·
              refine ⟨5583962603052005447351141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3722641735368003631567427 5583962603052005447351141)
              ·
                refine ⟨1046992988072251021378339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5583962603052005447351141 1046992988072251021378339)
                ·
                  refine ⟨1570489482108376532067509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1046992988072251021378339 1570489482108376532067509)
                  ·
                    refine ⟨147233388947660299881329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1570489482108376532067509 147233388947660299881329)
                    ·
                      rfl

theorem cell22_430104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_430104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_430104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_430104 prefixEnd_430104 := by exact prefixLift 430104
  have htrace : WordTrace (prefixWord ++ tailWord_430104) baseStart_430104 baseEnd_430104 := by
    simpa [prefixWord, tailWord_430104, baseEnd_430104] using wordTrace_append hprefix tailTrace_430104
  have hstable : (prefixWord ++ tailWord_430104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430104).length < 2 ^ (prefixWord ++ tailWord_430104).sum := by decide
  have hdescent : baseEnd_430104 < baseStart_430104 := by decide
  rcases family_descends (prefixWord ++ tailWord_430104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430106 : List Nat := [3, 1, 1, 3, 1, 3, 1, 5, 4]
def baseStart_430106 : Nat := 118140960795 + 430106 * 2 ^ 59
def prefixEnd_430106 : Nat := 4983230072969 + 3 ^ 40 * 430106 * 2
def baseEnd_430106 : Nat := 49078024529510987110441

theorem tailTrace_430106 : CollatzResearch.WordTrace tailWord_430106 prefixEnd_430106 49078024529510987110441 := by
  unfold tailWord_430106
  simp only [CollatzResearch.WordTrace]
  refine ⟨3921813644951723275439543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10458169719871262067838781 3921813644951723275439543)
  ·
    refine ⟨5882720467427584913159315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3921813644951723275439543 5882720467427584913159315)
    ·
      refine ⟨8824080701141377369738973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5882720467427584913159315 8824080701141377369738973)
      ·
        refine ⟨3309030262928016513652115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8824080701141377369738973 3309030262928016513652115)
        ·
          refine ⟨4963545394392024770478173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3309030262928016513652115 4963545394392024770478173)
          ·
            refine ⟨1861329522897009288929315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4963545394392024770478173 1861329522897009288929315)
            ·
              refine ⟨2791994284345513933393973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1861329522897009288929315 2791994284345513933393973)
              ·
                refine ⟨261749464157391931255685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2791994284345513933393973 261749464157391931255685)
                ·
                  refine ⟨49078024529510987110441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 261749464157391931255685 49078024529510987110441)
                  ·
                    rfl

theorem cell22_430106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 5, 4].length) (baseStart_430106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_430106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_430106 prefixEnd_430106 := by exact prefixLift 430106
  have htrace : WordTrace (prefixWord ++ tailWord_430106) baseStart_430106 baseEnd_430106 := by
    simpa [prefixWord, tailWord_430106, baseEnd_430106] using wordTrace_append hprefix tailTrace_430106
  have hstable : (prefixWord ++ tailWord_430106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430106).length < 2 ^ (prefixWord ++ tailWord_430106).sum := by decide
  have hdescent : baseEnd_430106 < baseStart_430106 := by decide
  rcases family_descends (prefixWord ++ tailWord_430106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430108 : List Nat := [2, 2, 3, 1, 3, 1, 4, 1, 1, 4]
def baseStart_430108 : Nat := 118140960795 + 430108 * 2 ^ 59
def prefixEnd_430108 : Nat := 4983230072969 + 3 ^ 40 * 430108 * 2
def baseEnd_430108 : Nat := 147234758229405622781317

theorem tailTrace_430108 : CollatzResearch.WordTrace tailWord_430108 prefixEnd_430108 147234758229405622781317 := by
  unfold tailWord_430108
  simp only [CollatzResearch.WordTrace]
  refine ⟨7843663762899823721665489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10458218350533098295553985 7843663762899823721665489)
  ·
    refine ⟨5882747822174867791249117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7843663762899823721665489 5882747822174867791249117)
    ·
      refine ⟨2206030433315575421718419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5882747822174867791249117 2206030433315575421718419)
      ·
        refine ⟨3309045649973363132577629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2206030433315575421718419 3309045649973363132577629)
        ·
          refine ⟨1240892118740011174716611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3309045649973363132577629 1240892118740011174716611)
          ·
            refine ⟨1861338178110016762074917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1240892118740011174716611 1861338178110016762074917)
            ·
              refine ⟨349000908395628142889047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1861338178110016762074917 349000908395628142889047)
              ·
                refine ⟨523501362593442214333571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349000908395628142889047 523501362593442214333571)
                ·
                  refine ⟨785252043890163321500357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 523501362593442214333571 785252043890163321500357)
                  ·
                    refine ⟨147234758229405622781317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 785252043890163321500357 147234758229405622781317)
                    ·
                      rfl

theorem cell22_430108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_430108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_430108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_430108 prefixEnd_430108 := by exact prefixLift 430108
  have htrace : WordTrace (prefixWord ++ tailWord_430108) baseStart_430108 baseEnd_430108 := by
    simpa [prefixWord, tailWord_430108, baseEnd_430108] using wordTrace_append hprefix tailTrace_430108
  have hstable : (prefixWord ++ tailWord_430108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430108).length < 2 ^ (prefixWord ++ tailWord_430108).sum := by decide
  have hdescent : baseEnd_430108 < baseStart_430108 := by decide
  rcases family_descends (prefixWord ++ tailWord_430108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_430164 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 1, 8]
def baseStart_430164 : Nat := 118140960795 + 430164 * 2 ^ 59
def prefixEnd_430164 : Nat := 4983230072969 + 3 ^ 40 * 430164 * 2
def baseEnd_430164 : Nat := 147253928173840143381145

theorem tailTrace_430164 : CollatzResearch.WordTrace tailWord_430164 prefixEnd_430164 147253928173840143381145 := by
  unfold tailWord_430164
  simp only [CollatzResearch.WordTrace]
  refine ⟨7844685006798384503684773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10459580009064512671579697 7844685006798384503684773)
  ·
    refine ⟨1470878438774697094440895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7844685006798384503684773 1470878438774697094440895)
    ·
      refine ⟨2206317658162045641661343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1470878438774697094440895 2206317658162045641661343)
      ·
        refine ⟨3309476487243068462492015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2206317658162045641661343 3309476487243068462492015)
        ·
          refine ⟨4964214730864602693738023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3309476487243068462492015 4964214730864602693738023)
          ·
            refine ⟨7446322096296904040607035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4964214730864602693738023 7446322096296904040607035)
            ·
              refine ⟨11169483144445356060910553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7446322096296904040607035 11169483144445356060910553)
              ·
                refine ⟨8377112358334017045682915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11169483144445356060910553 8377112358334017045682915)
                ·
                  refine ⟨12565668537501025568524373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8377112358334017045682915 12565668537501025568524373)
                  ·
                    refine ⟨147253928173840143381145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12565668537501025568524373 147253928173840143381145)
                    ·
                      rfl

theorem cell22_430164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_430164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_430164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_430164 prefixEnd_430164 := by exact prefixLift 430164
  have htrace : WordTrace (prefixWord ++ tailWord_430164) baseStart_430164 baseEnd_430164 := by
    simpa [prefixWord, tailWord_430164, baseEnd_430164] using wordTrace_append hprefix tailTrace_430164
  have hstable : (prefixWord ++ tailWord_430164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_430164).length < 2 ^ (prefixWord ++ tailWord_430164).sum := by decide
  have hdescent : baseEnd_430164 < baseStart_430164 := by decide
  rcases family_descends (prefixWord ++ tailWord_430164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
